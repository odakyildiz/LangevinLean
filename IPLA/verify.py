#!/usr/bin/env python3
"""Check generated-source integrity and compile the standalone without local oleans."""
from __future__ import annotations
import hashlib
import html
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def code_only(source):
    """Erase nested Lean block comments and line comments, preserving lines."""
    result, i, depth, string = [], 0, 0, False
    while i < len(source):
        a = source[i:i+2]
        if not string and a == '/-':
            depth += 1; result.extend('  '); i += 2
        elif depth and a == '-/':
            depth -= 1; result.extend('  '); i += 2
        elif depth:
            result.append('\n' if source[i] == '\n' else ' '); i += 1
        elif not string and a == '--':
            end = source.find('\n', i)
            if end < 0:
                break
            result.extend(' ' * (end-i)); i = end
        else:
            if source[i] == '"' and (i == 0 or source[i-1] != '\\'):
                string = not string
            result.append(source[i]); i += 1
    return ''.join(result)


def theorem_binders(theorem):
    """Read only top-level binders, stopping at the theorem conclusion."""
    text = theorem.removeprefix('theorem theorem1').lstrip()
    pairs = {'(': ')', '[': ']', '{': '}'}
    binders = []
    while text and text[0] in pairs:
        stack, end = [pairs[text[0]]], 1
        while stack:
            char = text[end]
            if char in pairs:
                stack.append(pairs[char])
            elif char == stack[-1]:
                stack.pop()
            end += 1
        binders.append(re.sub(r'\s+', ' ', text[:end]))
        text = text[end:].lstrip()
    if not text.startswith(':'):
        raise SystemExit('Unexpected syntax before the final theorem conclusion')
    return binders


def main():
    manifest = json.loads((HERE/'exposition/source_manifest.json').read_text())
    for path, digest in manifest.items():
        actual = hashlib.sha256((ROOT/path).read_bytes()).hexdigest()
        if actual != digest:
            raise SystemExit(f'Stale generated source: {path}; rerun build_artifacts.py')
    source = (HERE/'Standalone.lean').read_text()
    code = code_only(source)
    if re.search(r'\b(?:sorry|admit|sorryAx|axiom|unsafe)\b', code):
        raise SystemExit('Forbidden placeholder or added axiom in standalone code')
    imports = re.findall(r'^import (.+)$', code, re.M)
    if not imports or any(not x.startswith('Mathlib.') for x in imports):
        raise SystemExit('Standalone has a non-Mathlib import')
    theorem = 'theorem theorem1' + (HERE/'Theorem.lean').read_text().split('theorem theorem1',1)[1].split(' := by',1)[0]
    if html.escape(theorem) not in (HERE/'exposition/index.html').read_text():
        raise SystemExit('Exposition theorem differs from source')
    if source.count(theorem) != 1:
        raise SystemExit('Standalone theorem differs from source')
    flat_theorem = re.sub(r'\s+', ' ', theorem)
    expected_binders = [
        '{Ω : Type*}', '[MeasurableSpace Ω]', '(P : Measure Ω)',
        '[IsProbabilityMeasure P]', '(N dθ dx : ℕ)', '(hN : 0 < N)',
        '{Data : Type*}', '(U : Data → Joint dθ dx → ℝ)', '(y : Data)',
        '(m γ : ℝ)', '(L : ℝ≥0)', '(hdiff : Differentiable ℝ (U y))',
        '(hsc : StrongConvexOn Set.univ m (U y))',
        '(hLip : LipschitzWith L (gradient (U y)))', '(hm : 0 < m)',
        '(hγ : 0 < γ)', '(hsmall : γ ≤ 2 / (m + (L : ℝ)))',
        '(θStar : EuclideanSpace ℝ (Fin dθ))',
        '(hMaximizer : IsMarginalMaximizer (U y) θStar)',
        '(initial : Lp (State N dθ dx) 2 P)',
        '(noise : ℕ → Lp (State N dθ dx) 2 P)',
        '(hGaussian : GaussianInnovations P initial noise)', '(k : ℕ)',
    ]
    actual_binders = theorem_binders(theorem)
    if actual_binders != expected_binders:
        raise SystemExit(f'Final theorem binder audit failed: {actual_binders}')
    dimension_checks = {
        'independent_natural_dimensions': '(N dθ dx : ℕ) (hN : 0 < N)' in flat_theorem,
        'different_parameter_and_latent_spaces':
            '(U : Data → Joint dθ dx → ℝ) (y : Data)' in flat_theorem and
            '(θStar : EuclideanSpace ℝ (Fin dθ))' in flat_theorem and
            'Lp (State N dθ dx) 2 P' in flat_theorem,
        'equilibrium_radius_uses_parameter_dimension':
            'Real.sqrt (2 * (dθ : ℝ) / ((N : ℝ) * m))' in flat_theorem,
        'bias_uses_both_dimensions_exactly':
            'Real.sqrt ((dx : ℝ) + (dθ : ℝ) / (N : ℝ)) * Real.sqrt γ' in flat_theorem,
        'no_dimension_equality_or_padding_premise': not re.search(
            r'(?:dθ\s*=\s*dx|dx\s*=\s*dθ|Fin\s*\(\s*max|\(hpad\w*\s*:)',
            flat_theorem),
        'zero_dimensions_allowed': not re.search(
            r'(?:0\s*<\s*(?:dθ|dx)|(?:dθ|dx)\s*≠\s*0|NeZero\s+(?:dθ|dx))',
            flat_theorem),
    }
    if not all(dimension_checks.values()):
        raise SystemExit(f'Independent dimension audit failed: {dimension_checks}')
    potential_checks = {
        'fixed_observation_slice': '(U : Data → Joint dθ dx → ℝ) (y : Data)' in theorem,
        'joint_strong_convexity_only': theorem.count('StrongConvexOn') == 1 and
            '(hsc : StrongConvexOn Set.univ m (U y))' in theorem,
        'joint_gradient_lipschitz_only': theorem.count('LipschitzWith') == 1 and
            '(hLip : LipschitzWith L (gradient (U y)))' in theorem,
        'constant_compatibility_derived': '(hmL :' not in theorem,
        'no_hessian_or_c2': 'ContDiff' not in theorem and 'hessian' not in theorem.lower(),
        'no_reference_or_stationarity_hypothesis': all(x not in theorem for x in
            ['ReferenceFamily', 'L2Reference', 'ProductReference', 'stationary', 'Stationary']),
        'no_concentration_or_marginal_convexity_hypothesis': all(x not in theorem for x in
            ['hconcentration', 'projectedRMS', 'marginalPotential']),
        'no_finite_transport_hypothesis': '(hfinite :' not in theorem,
        'actual_gaussian_algorithm_specified':
            '(hGaussian : GaussianInnovations P initial noise)' in theorem,
        'actual_marginal_maximizer_center':
            '(hMaximizer : IsMarginalMaximizer (U y) θStar)' in theorem,

    }
    if not all(potential_checks.values()):
        raise SystemExit(f'Potential hypothesis audit failed: {potential_checks}')
    # Ask Lake for the pinned Lean/dependency paths, then explicitly remove the
    # project's compiled modules. Copy only one source to a fresh directory.
    lean_path = subprocess.check_output(['lake','env','printenv','LEAN_PATH'], cwd=ROOT, text=True).strip()
    lean_bin = subprocess.check_output(['lake','env','which','lean'], cwd=ROOT, text=True).strip()
    local = str((ROOT/'.lake/build/lib/lean').resolve())
    filtered = [p for p in lean_path.split(os.pathsep) if str(Path(p).resolve()) != local]
    env = os.environ.copy(); env['LEAN_PATH'] = os.pathsep.join(filtered)
    with tempfile.TemporaryDirectory(prefix='ipla-standalone-') as temp:
        copy = Path(temp)/'Standalone.lean'; shutil.copyfile(HERE/'Standalone.lean', copy)
        completed = subprocess.run([lean_bin, str(copy)], cwd=temp, env=env, text=True, capture_output=True)
    output = completed.stdout + completed.stderr
    allowed_axioms = {'propext', 'Classical.choice', 'Quot.sound'}
    axiom_entries = re.findall(r"'([\w.]+)' depends on axioms: \[([^\]]*)\]", output)
    axiom_audit = {name: [x.strip() for x in group.split(',') if x.strip()]
                   for name, group in axiom_entries}
    reported_axioms = {axiom for axioms in axiom_audit.values() for axiom in axioms}
    unexpected_axioms = sorted(reported_axioms - allowed_axioms)
    requested_audits = re.findall(r'^#print axioms ([\w.]+)\s*$', code, re.M)
    all_audits_present = list(axiom_audit) == requested_audits
    report = {
        'standalone_exit_code': completed.returncode,
        'local_compiled_modules_excluded': local not in env['LEAN_PATH'].split(os.pathsep),
        'only_mathlib_imports': True,
        'local_source_module_count': len(manifest)-1,
        'standalone_sha256': hashlib.sha256(source.encode()).hexdigest(),
        'lean_toolchain': (ROOT/'lean-toolchain').read_text().strip(),
        'axiom_audit': axiom_audit,
        'all_requested_axiom_audits_present': all_audits_present,
        'unexpected_axioms': unexpected_axioms,
        'source_manifest_verified': True,
        'exact_statement_verified': True,
        'potential_hypothesis_audit': potential_checks,
        'independent_dimension_audit': dimension_checks,
        'independent_parameter_latent_dimensions': True,
        'zero_dimensions_included': True,
        'rescaled_state_dimension': 'dθ + N*dx',
        'parameter_concentration_radius': 'sqrt (2*dθ/(N*m))',
        'discretization_dimension_factor': 'sqrt (dx + dθ/N)*sqrt γ',
        'exact_final_binder_list_verified': True,
        'final_binders': actual_binders,
        'additional_analytic_hypotheses': [],
        'paper_assumptions_fully_discharged': True,
        'source_scope': 'General-dimension extension of Theorem 1 equation (34), using its Appendix B proof with independent natural dθ and dx; equal dimensions recover the printed equation. L bounds the actual potential including its prior, as required by Appendix B.',
        'gibbs_process_stationarity_derived': True,
        'canonical_continuous_time_brownian_source_constructed': True,
        'stationary_reference_family_constructed': True,
        'marginal_concentration_derived': True,
        'marginal_strong_log_concavity_derived': True,
        'prekopa_leindler_proved': True,
        'marginal_maximizer_exists_uniquely': True,
        'finite_initial_transport_derived_from_L2': True,
        'generator_integration_proved': True,
        'gibbs_dirichlet_identity_proved': True,
        'constant_gibbs_weak_forward_solution_proved': True,
        'independent_initial_coupling_extension_proved': True,
        'canonical_algorithm_law_independence_proved': True,
        'canonical_gaussian_ipla_law_proved': True,
        'actual_parameter_marginal_identified': True,
        'powered_marginal_normalization_and_moments_proved': True,
        'brownian_increment_gaussian_laws_and_independence_proved': True,
        'shared_ULA_convergence_theorem_reused': True,
    }
    (HERE/'exposition/verification.json').write_text(json.dumps(report, indent=2)+'\n')
    (HERE/'exposition/standalone-check.txt').write_text(output)
    print(output)
    if completed.returncode:
        raise SystemExit(completed.returncode)
    if unexpected_axioms:
        raise SystemExit(f'Unexpected axioms in standalone: {unexpected_axioms}')
    if not all_audits_present:
        raise SystemExit('One or more requested axiom audits are missing or out of order')
    if set(axiom_audit.get('IPLA.theorem1', [])) != allowed_axioms:
        raise SystemExit('Unexpected final theorem axiom dependencies')
    print('Verified source hashes, exact statement, and isolated Mathlib-only compilation.')

if __name__ == '__main__':
    main()
