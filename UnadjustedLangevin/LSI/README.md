# ULA under the log-Sobolev inequality

This development follows [Vempala–Wibisono (2019), *Rapid Convergence of the
Unadjusted Langevin Algorithm: Isoperimetry Suffices*, Theorem 2](https://proceedings.neurips.cc/paper_files/paper/2019/file/65a99bb7a3115fdede20da98b08a370f-Paper.pdf).
For a target $\nu\propto e^{-U}$ satisfying LSI with constant $\alpha>0$
and an $L$-Lipschitz gradient, the published bound is

$$
0<h\le\frac{\alpha}{4L^2}
\quad\Longrightarrow\quad
H_\nu(\rho_k)\le e^{-\alpha hk}H_\nu(\rho_0)
  +\frac{8hnL^2}{\alpha}.
$$

Here $\rho_k$ is the law of the independent-Gaussian ULA update
$X_{k+1}=X_k-h\nabla U(X_k)+\sqrt{2h}\,Z_k$ in dimension $n$.

**Formalization status: conditional.** The endpoint
`ULA.LSI.ula_kl_bound_of_interpolation` in [Theorem.lean](Theorem.lean)
proves this bound for the actual ULA laws from explicit analytic interpolation
hypotheses. A proof from only the paper's LSI and smoothness assumptions remains
incomplete. The current endpoint additionally takes $\alpha\le L$ as an input.
The wrapper `ULA.LSI.ula_kl_bound_of_regular_interpolation` in
[RegularizedTheorem.lean](RegularizedTheorem.lean) derives the entropy
derivatives and production estimate from density regularity and a weak equation;
its law identification, drift-energy, and gradient-moment inputs remain explicit.

## Entropy and normalization

For a relative probability density $r>0$, write $\rho=r\nu$. The definitions use
Mathlib's actual extended KL divergence and relative Fisher information:

$$
H_\nu(\rho)=\int r\log r\,d\nu,
\qquad
J_\nu(\rho)=\int\|\nabla\log r\|^2\,d\rho,
\qquad
2\alpha H_\nu(\rho)\le J_\nu(\rho).
$$

The LSI test class consists of strictly positive continuously differentiable
relative probability densities; extension to arbitrary densities by approximation
is a separate task. Finiteness of both KL and Fisher information is retained
before their `ENNReal.toReal` values are used.

The scalar one-step calculation proves the paper's coefficient $6$,

$$
H_\nu(\rho_{k+1})\le e^{-\alpha h}H_\nu(\rho_k)+6h^2nL^2,
$$

from the interpolation production and gradient-moment estimates. Iteration
then gives the coefficient $8$ in the displayed theorem.

## Modules

| Module | Proved content |
| --- | --- |
| [FunctionalInequality.lean](FunctionalInequality.lean) | LSI for a probability target using actual KL and the relative score. |
| [KLOfDensity.lean](KLOfDensity.lean) | Radon–Nikodym identification, finite KL from integrability of $r\log r$, and weighted entropy/Fisher formulas. |
| [EntropyDerivative.lean](EntropyDerivative.lean) | Differentiation of the entropy integral under explicit local domination. |
| [ScoreCalculus.lean](ScoreCalculus.lean) | Gradient identities and the entropy test of an admissible weak Fokker–Planck equation. |
| [DriftError.lean](DriftError.lean) | Integrated Young inequality and the production bound $-3J/4+$ drift-error energy. |
| [Regularity.lean](Regularity.lean) | `LocalEntropyRegularity` supplies dominated differentiation; normalized density paths yield actual-KL continuity and right derivatives, and an admissible weak equation yields their Fisher/drift production bound. |
| [EntropyDecay.lean](EntropyDecay.lean) | Scalar differential comparison, including constant forcing. |
| [EntropyFlow.lean](EntropyFlow.lean) | Conditional continuous-time decay of actual KL at rate $2\alpha$. |
| [ULALaw.lean](ULALaw.lean) | Actual Gaussian ULA laws, the frozen-drift interpolation, probability preservation, and endpoint identification. |
| [GaussianDrift.lean](GaussianDrift.lean) | Exact displacement moments and the joint gradient-error energy bound for the actual independent-Gaussian interpolation. |
| [OneStep.lean](OneStep.lean) | The coefficient-$6$ scalar estimate from explicit interpolation primitives. |
| [DiscreteEntropy.lean](DiscreteEntropy.lean) | Exact recurrence iteration and the coefficient-$8$ envelope. |
| [Theorem.lean](Theorem.lean) | Conditional one-step and iterated KL bounds for the actual ULA laws. |
| [RegularizedTheorem.lean](RegularizedTheorem.lean) | The same conditional KL bound, deriving entropy regularity and production from local density data and an admissible weak equation. |
| [Check.lean](Check.lean) | Kernel axiom-dependency audit of the conditional development. |

## Remaining analytic obligations

The endpoint requires a positive smooth density path identified with the actual
frozen-drift law at every interpolation time, finite KL and Fisher information,
entropy continuity and right derivatives, the entropy-production estimate, and
a differentiable potential with an integrable squared-gradient moment satisfying

$$
\mathbb E_{\rho_k}\|\nabla U\|^2
\le\frac{4L^2}{\alpha}H_\nu(\rho_k)+2nL.
$$

`Regularity` derives actual-KL continuity and right derivatives from local
domination and pointwise density derivatives; the KL derivative is a conclusion
of these data. Together with `ScoreCalculus` and `DriftError`, it derives the
Fisher/drift production bound from an admissible forced weak equation and
integrable drift-error energy. Applying these results still needs
the construction and regularity of the actual Gaussian interpolation density,
and its weak equation for the noncompact entropy test. A compact-test generator
identity alone does not supply the admissibility of this test.

`GaussianDrift` proves the displacement and gradient-error energy estimates on
the actual joint law $\rho_k\otimes\mathcal N(0,I)$. The remaining link is to
identify the weak equation's drift-error field as a conditional mean of that
joint gradient discrepancy and prove the conditional Jensen bound that
transfers its energy estimate to the density-level error field.

`LocalEntropyRegularity` currently requires a two-sided time neighborhood,
including at $t=0$. The Gaussian interpolation naturally starts at $t=0$;
an appropriate extension or a one-sided endpoint regularity argument remains
part of the density construction.

The gradient-moment estimate and the compatibility $\alpha\le L$ remain
explicit inputs. The LSI-to-Talagrand step used in the paper's route to the
gradient-moment estimate is also unformalized.

Compile the full development from the repository root:

```sh
lake build +UnadjustedLangevin.LSI.Check
lake env lean UnadjustedLangevin/LSI/Check.lean
```
