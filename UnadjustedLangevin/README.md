# Unadjusted Langevin: Dalalyan's theorem in Lean

The end-to-end strongly convex Gaussian ULA theorem is kernel-checked, including
both sharp step-size regimes and the corrected constant **1.65**. The public
endpoints construct the reference process and prove its Gibbs stationarity.
They take no stationary-reference, generator-uniqueness, score-moment, target
normalization, or Brownian-existence hypothesis.

## Build and inspect

Run from the repository root:

```sh
lake build
lake env lean UnadjustedLangevin/Check.lean
python3 UnadjustedLangevin/exposition/build_document.py
python3 UnadjustedLangevin/exposition/verify_document.py
```

Import `UnadjustedLangevin` to use the library. The pinned toolchain is Lean
4.35.0-rc3 with mathlib v4.35.0-rc3. Kernel audits report only the standard
`propext`, `Classical.choice`, and `Quot.sound` dependencies.

## Public statements

`ULA.Hilbert.dalalyan` proves, for `0 < h ≤ 2 / (m + L)`,

```text
W₂(ULA_hⁿ μ, π) ≤ (1 − mh)ⁿ W₂(μ, π) + 1.65 (L/m) √(hd).
```

`ULA.Hilbert.dalalyan_large_step` proves, for `2 / (m + L) ≤ h` and `hL < 2`,

```text
W₂(ULA_hⁿ μ, π) ≤ (Lh − 1)ⁿ W₂(μ, π) + 1.65 Lh/(2 − Lh) √(hd).
```

Here π is the normalized Gibbs law proportional to exp(−U), `d` is the
Euclidean dimension, and `ULA_h` is the actual product-Gaussian update
`x ↦ x − h∇U(x) + √(2h) ξ` on laws. The potential assumptions are exactly
`Differentiable ℝ U`, positive m-strong convexity of U, and a globally
L-Lipschitz gradient of U. No Hessian or C² assumption on U is introduced.
The dimension is finite and nonzero. The initial law is a probability measure
with finite initial W₂; its finite second moment follows from that hypothesis
and the proved Gibbs second moment.

`ULA.Hilbert.dalalyan_of_gaussian_innovations` and
`dalalyan_large_step_of_gaussian_innovations` in `GaussianULA.lean` give the
same bounds for the defined `lpChain` on any supplied probability space.
They use the actual standard Gaussian law of every innovation coordinate,
independence across all iteration-coordinate pairs, and independence of the
initial state from the whole noise sequence. Grouping coordinates into iid
Gaussian vectors and identifying every algorithm output law are proved.
Finite initial W₂ is derived from the actual L² initialization.

`dalalyan_output_finite` proves finite output transport cost. The real-valued
bounds therefore do not conceal infinite costs behind `ENNReal.toReal`.

## How the former hypotheses are discharged

| Modules | Checked content |
| --- | --- |
| `StrongConvexity`, `Analysis/Smooth`, `SharpContraction`, `PotentialAssumptions` | Shared quadratic lower and upper bounds, both sharp Euler contractions, and m≤L in nonzero dimension. |
| `Gibbs`, `GibbsScore`, `StationaryMoments`, `GibbsConcentration` | Finite positive normalization, Gibbs moments, sharp score bound, and mode concentration. |
| `Generator`, `GeneratorDirichlet` | Integration of the generator, absolute integrability, Dirichlet identity, symmetry, and dissipativity for compact C² tests. |
| `CanonicalBrownian`, `GaussianHilbert`, `LpCharacteristic` | An explicit independent Brownian source from Gaussian series, with its finite-dimensional laws proved. |
| `LangevinIntegral`, `LangevinUniqueness`, `BrownianLangevin` | Finite-horizon continuous L² integral solutions, uniqueness, and exact Brownian noise moments. |
| `GaussianProposalDensity`, `GaussianProposalPairDensity`, `Metropolis`, `MALAInvariance` | The actual Gaussian proposal density and exact Gibbs invariance of the Metropolis-adjusted step. |
| `MALAError`, `MALACoupling`, `EulerLimit`, `CouplingLimit`, `GibbsStationarity` | Vanishing rejection error, a stationary coupling, matching-noise Euler convergence, and Gibbs stationarity of the actual integral solution. |
| `BrownianSegmentsGlobal`, `ProductBrownian`, `CanonicalULA` | Segment consistency and complete stationary reference construction on every initial-coupling extension. |
| `InitialCoupling`, `InitialExtension`, `TransportMoments` | Exact initial coupling/cost, independent product extension, moment transfer, and the initial transport infimum. |
| `ChainLaw`, `MarkovLaw`, `GaussianInnovationVectors`, `GaussianULA` | Canonical iid recursion law, Markov iteration, scalar-to-vector Gaussian identification, and actual-algorithm convergence. |
| `LocalError`, `Recurrence`, `HilbertDalalyan`, `ReferenceFamily`, `ProductReference` | The checked local error constant and both transport bounds, including the infimum over initial couplings. |

Each table entry abbreviates a `.lean` filename. Older conditional
`L2Reference` and `ReferenceFamily` lemmas remain useful intermediate results;
the public theorems construct their inputs. No optimal coupling is assumed.
The transport development proves the properties used here without claiming a
complete Wasserstein metric theory.

## Generator integration and actual stationarity

For compactly supported C² test functions, ordinary integration by parts gives

```text
∫ (Δφ − ⟨∇U,∇φ⟩) dπ = 0,
∫ φ Lψ dπ = −∫ ⟨∇φ,∇ψ⟩ dπ.
```

Only exp(−U)'s first derivative is used. The C² condition belongs to the test
functions. These identities alone do not identify the law of a constructed
process, so the formal proof also supplies that identification.

The actual Gaussian Metropolis step preserves Gibbs by detailed balance. Its
expected rejected displacement is bounded by C h√h under the original
potential assumptions. A synchronous coupling compares n ULA steps to this
stationary chain with expected distance at most n C h√h. On a fixed horizon,
`h=T/n`, this tends to zero. Deterministic Banach-space Euler convergence
identifies the limit with the constructed L² Langevin solution, and
characteristic functions identify its Gibbs law. This completes stationarity
without assuming a Dynkin formula or weak-forward-equation uniqueness.

The integral solution is a continuous curve in L² with a Bochner integral
equation. This suffices for the convergence theorem. A separate sample-path
SDE representation is not an input to any public endpoint.

See [the complete hypothesis audit](exposition/hypotheses.md). The IPLA
application additionally proves marginal strong log-concavity and its sharp
concentration radius from the same joint-potential assumptions.

## Reference and constant

The separate [ULA analysis under LSI](LSI/README.md) follows
[Vempala–Wibisono (2019), Theorem 2](https://proceedings.neurips.cc/paper_files/paper/2019/file/65a99bb7a3115fdede20da98b08a370f-Paper.pdf).
For $0<h\le\alpha/(4L^2)$, its published KL bound is

$$
H_\nu(\rho_k)\le e^{-\alpha hk}H_\nu(\rho_0)+\frac{8hnL^2}{\alpha}.
$$

`ULA.LSI.ula_kl_bound_of_interpolation` proves this bound for the actual Gaussian
ULA laws **conditionally** on identified interpolation densities, regularity,
finite KL/Fisher information, entropy production, a gradient-moment estimate,
and $\alpha\le L$. The modules prove the entropy calculus, actual Gaussian
displacement/error moments, one-step scalar estimate, and iteration. A second
wrapper derives KL regularity and production
from local density data and an admissible weak equation. Deriving every
interpolation and moment obligation
from LSI and smoothness alone remains unfinished; see the guide's precise
status and module map. The strongly convex transport endpoints above remain
the complete results under their stated potential assumptions.

The coupling estimate follows Section 6 of
[Dalalyan (COLT 2017)](https://proceedings.mlr.press/v65/dalalyan17a.html).
The corrected coefficient from
[Dalalyan–Karagulyan](https://arxiv.org/abs/1710.00095) is derived independently
in Lean: `(7/6) √2 ≤ 33/20 = 1.65`.

A fixed positive step gives a nonzero error floor. The bounds do not assert
exact Gibbs convergence as n tends to infinity at fixed h.

## Proof document

Open `exposition/dist/index.html` directly in a browser. The offline document
presents mathematical statements with exact Lean source and complete
proof-line coverage. Its generator and verifier check source hashes, displayed
lines, and local links. See `exposition/README.md` for regeneration.
