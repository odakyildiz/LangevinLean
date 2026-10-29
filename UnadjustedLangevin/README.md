# Unadjusted Langevin: Dalalyan's theorem in Lean

The strongly convex Gaussian ULA theorem is proved in Lean, with both step-size
regimes and the coefficient **$1.65$**. The proof constructs the reference
process, proves that its distribution is the normalized Gibbs measure at every
time, and bounds its gradient second moment. These properties follow from the
stated assumptions on the potential.

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

`ULA.Hilbert.dalalyan` proves, for $0<h\le2/(m+L)$,

$$
W_2(\operatorname{ULA}_h^n\mu,\pi)
\le(1-mh)^nW_2(\mu,\pi)+1.65\frac Lm\sqrt{hd}.
$$

`ULA.Hilbert.dalalyan_large_step` proves, for $2/(m+L)\le h$ and $hL<2$,

$$
W_2(\operatorname{ULA}_h^n\mu,\pi)
\le(Lh-1)^nW_2(\mu,\pi)+1.65\frac{Lh}{2-Lh}\sqrt{hd}.
$$

Here $\pi$ is the normalized Gibbs law proportional to $e^{-U}$, $d$ is the
Euclidean dimension, and $\operatorname{ULA}_h$ is the actual product-Gaussian update
$x\mapsto x-h\nabla U(x)+\sqrt{2h}\,\xi$ on laws. The potential assumptions are exactly
`Differentiable ℝ U`, positive $m$-strong convexity of $U$, and a globally
$L$-Lipschitz gradient of $U$. No Hessian or $C^2$ assumption on $U$ is introduced.
The dimension is finite and nonzero. The initial law is a probability measure
with finite initial $W_2$; its finite second moment follows from that hypothesis
and the proved Gibbs second moment.

`ULA.Hilbert.dalalyan_of_gaussian_innovations` and
`dalalyan_large_step_of_gaussian_innovations` in `GaussianULA.lean` give the
same bounds for the defined `lpChain` on any supplied probability space.
They use the actual standard Gaussian law of every innovation coordinate,
independence across all iteration-coordinate pairs, and independence of the
initial state from the whole noise sequence. Grouping coordinates into iid
Gaussian vectors and identifying every algorithm output law are proved.
Finite initial $W_2$ is derived from the actual $L^2$ initialization.

`dalalyan_output_finite` proves finite output transport cost. The real-valued
bounds therefore do not conceal infinite costs behind `ENNReal.toReal`.

## Supporting results

| Modules | Checked content |
| --- | --- |
| `StrongConvexity`, `Analysis/Smooth`, `SharpContraction`, `PotentialAssumptions` | Shared quadratic lower and upper bounds, both sharp Euler contractions, and $m\le L$ in nonzero dimension. |
| `Gibbs`, `GibbsScore`, `StationaryMoments`, `GibbsConcentration` | Finite positive normalization, Gibbs moments, sharp score bound, and mode concentration. |
| `Generator`, `GeneratorDirichlet` | Integration of the generator, absolute integrability, Dirichlet identity, symmetry, and dissipativity for compact $C^2$ tests. |
| `CanonicalBrownian`, `GaussianHilbert`, `LpCharacteristic` | An explicit independent Brownian source from Gaussian series, with its finite-dimensional laws proved. |
| `LangevinIntegral`, `LangevinUniqueness`, `BrownianLangevin` | Finite-horizon continuous $L^2$ integral solutions, uniqueness, and exact Brownian noise moments. |
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

## Integration by parts and Gibbs stationarity

For compactly supported $C^2$ test functions, ordinary integration by parts gives

$$
\begin{aligned}
\int(\Delta\varphi-\langle\nabla U,\nabla\varphi\rangle)\,d\pi&=0,\\
\int\varphi L\psi\,d\pi&=-\int\langle\nabla\varphi,\nabla\psi\rangle\,d\pi.
\end{aligned}
$$

Only $e^{-U}$'s first derivative is used. The $C^2$ condition belongs to the test
functions. These identities alone do not identify the law of a constructed
process, so the formal proof also supplies that identification.

The actual Gaussian Metropolis step preserves Gibbs by detailed balance. Its
expected rejected displacement is bounded by $Ch\sqrt h$ under the original
potential assumptions. A synchronous coupling compares $n$ ULA steps to this
stationary chain with expected distance at most $nCh\sqrt h$. On a fixed horizon,
$h=T/n$, this tends to zero. Deterministic Banach-space Euler convergence
identifies the limit with the constructed $L^2$ Langevin solution, and
characteristic functions identify its Gibbs law. This completes stationarity
without assuming a Dynkin formula or weak-forward-equation uniqueness.

The integral solution is a continuous curve in $L^2$ satisfying a Bochner integral
equation. The convergence theorem uses this representation. It does not require
a separate theorem on continuity of the individual sample paths.

See [the complete hypothesis audit](exposition/hypotheses.md). The IPLA
application additionally proves marginal strong log-concavity and its sharp
concentration radius from the same joint-potential assumptions.

## Reference and constant

The separate [ULA proof under LSI](LSI/exposition/index.html) follows
[Vempala–Wibisono (2019), Theorem 2](https://proceedings.neurips.cc/paper_files/paper/2019/file/65a99bb7a3115fdede20da98b08a370f-Paper.pdf).
For $0<h\le\alpha/(4L^2)$, its published KL bound in dimension $n$ is

$$
H_\nu(\rho_k)\le e^{-\alpha hk}H_\nu(\rho_0)+\frac{8hnL^2}{\alpha}.
$$

`ULA.LSI.ula_kl_bound` proves this bound for the Gaussian ULA distributions
from a normalized Gibbs target satisfying LSI, differentiability of the
potential, a Lipschitz gradient, the stated positive step restriction, and
finite initial relative entropy. The proof constructs and differentiates the
Gaussian interpolation density, bounds the gradient moments, proves the weak
equation and entropy derivative, and derives $\alpha\le L$ in positive
dimension. It then integrates the entropy inequality and sums the discrete
recurrence. In dimension zero the distributions are equal. Finiteness of KL at
each iterate is included in the conclusion. The earlier conditional theorem
`ULA.LSI.ula_kl_bound_of_interpolation` remains available with its explicit
interpolation assumptions. See the [module guide](LSI/README.md) for the proof
and source correspondence.

The coupling estimate follows Section 6 of
[Dalalyan (COLT 2017)](https://proceedings.mlr.press/v65/dalalyan17a.html).
The corrected coefficient from
[Dalalyan–Karagulyan](https://arxiv.org/abs/1710.00095) is derived independently
in Lean: $(7/6)\sqrt2\le33/20=1.65$.

For fixed positive step size, the bound tends to a positive constant as the
iteration count tends to infinity. That constant tends to zero with the step
size.

## Proof document

Open `exposition/dist/index.html` directly in a browser. The offline document
presents mathematical statements with exact Lean source and complete
proof-line coverage. Its generator and verifier check source hashes, displayed
lines, and local links. See `exposition/README.md` for regeneration.
