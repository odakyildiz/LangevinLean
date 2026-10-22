# ULA under the log-Sobolev inequality

Open the [detailed proof page](exposition/index.html) for the mathematical
argument beside every LSI declaration, complete source files, and a comparison
with the reference paper. The page works offline and offers mathematics-only
reading, foldable Lean proofs, and source search. Its
[build guide](exposition/README.md) explains how to regenerate and verify it.

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
its analytic inputs remain explicit. Additional bridge modules now construct the
positive-time Gaussian mixture and its Gibbs-relative density, prove positivity,
finiteness and spatial continuity, construct the conditional drift field and
its energy estimate, and derive the gradient-moment estimate from an explicit
entropy-cost coupling. These bridges do not yet construct all of the wrapper's
regularity and weak-equation data from LSI alone.

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
| [InterpolationDensity.lean](InterpolationDensity.lean) | Explicit positive-time Gaussian mixture and Gibbs-relative densities; actual-law identification, positivity, pointwise finiteness, normalization and spatial continuity, including from singular initial laws. |
| [ConditionalDrift.lean](ConditionalDrift.lean) | Construct the measurable conditional drift by Doob–Dynkin factorization; prove conditional Jensen, measurable-set flux and integrable inner-test identities, and the required density-weighted energy bound. |
| [GradientMoment.lean](GradientMoment.lean) | Derive gradient square integrability and the precise entropy-dependent moment bound from a finite-cost coupling with an explicit entropy-cost estimate, using the proved target score moment. |
| [InteriorEntropy.lean](InteriorEntropy.lean) | Affine comparison needing derivatives only at interior times; actual-KL derivative identification from positive-time local regularity. |
| [OneStep.lean](OneStep.lean) | The coefficient-$6$ scalar estimate from explicit interpolation primitives. |
| [DiscreteEntropy.lean](DiscreteEntropy.lean) | Exact recurrence iteration and the coefficient-$8$ envelope. |
| [Theorem.lean](Theorem.lean) | Conditional one-step and iterated KL bounds for the actual ULA laws. |
| [RegularizedTheorem.lean](RegularizedTheorem.lean) | The same conditional KL bound, deriving entropy regularity and production from local density data and an admissible weak equation. |
| [InterpolationData.lean](InterpolationData.lean) | Explicit analytic data reused by particle algorithms; derives finite KL, one-step and iterated estimates without assuming an entropy recurrence. |
| [Check.lean](Check.lean) | Kernel axiom-dependency audit of the conditional development. |

## Remaining analytic obligations

`InterpolationDensity` constructs the actual Gaussian mixture at every
positive time and the explicit relative density
$r_t(y)=Z e^{U(y)}q_t(y)$. Its law identity, strict positivity, pointwise
finiteness, normalization and spatial continuity are proved. This does not yet
supply spatial $C^1$ regularity, time differentiation, finite Fisher information,
or the uniform integrable domination needed for entropy differentiation.

`ConditionalDrift` constructs a strongly measurable field

$$
e_t(Y_t)=\mathbb E[\nabla U(Y_t)-\nabla U(X_0)\mid Y_t]
$$

and proves its squared-energy bound by conditional Jensen. It also proves
measurable-set flux identities and transfer of integrable noncompact
inner-product tests between the joint law and the state law. The remaining
weak-equation obligation is to prove the actual Gaussian interpolation's
forced Fokker–Planck identity and justify its entropy test. A compact-test
generator identity does not by itself establish admissibility of the
noncompact test $\log r_t+1$.

`LocalEntropyRegularity` derives actual-KL continuity and derivatives from
local dominated density data. The existing ULA endpoint requests these data
throughout $[0,h]$, including a two-sided neighborhood at zero.
`InteriorEntropy` proves an alternative scalar comparison using only interior
derivatives and endpoint continuity, together with a positive-time actual-KL
derivative theorem. These new lemmas do not change the existing endpoint's
initial-law interface; entropy continuity at zero and the full positive-time
analytic construction still need to be assembled.

`GradientMoment` proves, for any finite-cost coupling $c$ of $\rho$ with the
normalized Gibbs target,

$$
\mathbb E_\rho\|\nabla U\|^2
\le 2L^2\int\|x-y\|^2\,dc(x,y)+2nL,
$$

and derives square integrability of the gradient under $\rho$. An explicit
coupling estimate $\int\|x-y\|^2dc\le 2H_\nu(\rho)/\alpha$ then gives the exact
moment bound used by the ULA proof. The LSI-to-Talagrand implication that
provides such transport control remains unformalized, and the existing
endpoint still displays its gradient-moment input. The compatibility
$\alpha\le L$ also remains an explicit hypothesis.

Compile the full development from the repository root:

```sh
lake build +UnadjustedLangevin.LSI.Check
lake env lean UnadjustedLangevin/LSI/Check.lean
```
