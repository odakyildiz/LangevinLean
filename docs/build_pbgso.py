#!/usr/bin/env python3
"""PBGSO's source-based exposition, outside the published-report/PDF catalog.

All displayed Lean statements, complete declarations, shared contexts and the
assumption inventory are read from the current source. The source comparison is
explicit about source interpretations, integrability domains and actual process assumptions.
"""
from __future__ import annotations

import hashlib
import html
import json
from pathlib import Path
import re

from build_site import ROOT, HELPERS, anchor, code, commands, declarations, relative, shell, toolbar

E = html.escape
OVERVIEW = "PBGSO/exposition/index.html"
CATALOG = "PBGSO/exposition/technical.html"

MODULES = {
    "RawStationaryUniqueness": (
        "Stationary product-law uniqueness for the original raw equations",
        "Actual stationary original solution families, direct A1 strong existence and "
        "same-driver uniqueness instantiate the arbitrary-source contraction bounds. "
        "Exponential decay and Wasserstein separation give equality of the optimiser "
        "states and sampler laws.",
        "Assume P₂ stationary sampler laws, source A3 with positive rate, and the "
        "stated original stationary solution/A1 existence and uniqueness data on each "
        "finite horizon. The constant-diffusion branch additionally requires universal "
        "finite signed coupling work and primitive Borel fields; the linear-growth "
        "branch requires its canonical primitive coefficient regularity. No weak-generator "
        "realization, energy estimate or contraction conclusion is supplied."),
    "Framework": (
        "General optimiser–sampler model and weak stationarity",
        "The optimiser, parameter projection, sampler, position projection, observation map, "
        "drift and diffusion are independent inputs. The expected gradient is a Bochner integral; "
        "its empirical counterpart is proved equal to the finite average. Weak solutions obey "
        "the optimiser ODE and a generator forward equation for a specified test family.",
        "Stationarity assumes frozen generator stationarity, observation and test integrability, "
        "the vanishing mean gradient, an optimiser fixed point at every nonnegative time, and "
        "uniqueness of the stated weak equation. Strong SDE existence and equivalence to this "
        "weak formulation are additional analytic work."),
    "PaperTheorems": (
        "Twisted geometry and energy comparison theorems",
        "The joint monotonicity definition retains arbitrary optimiser maps and parameter- and "
        "state-dependent sampler diffusion. Grönwall and a regularized square-root argument "
        "prove decay and forced-energy comparison, with the metric condition number explicit.",
        "The comparison theorems take continuity, right derivative and dissipation inequalities "
        "for a supplied scalar energy. WeakContraction separately derives that energy inequality from "
        "the actual synchronous weak generator, and LawContraction passes it to Wasserstein "
        "distance. Strong-SDE equivalence and generator-domain justification remain separate. "
        "Sampling.lean proves the i.i.d. gradient-variance identity."),
    "Criteria": (
        "Small-gain, projected-field and hypocoercive algebra",
        "Completed squares verify scalar small-gain conditions. Projected work inequalities "
        "combine with auxiliary dissipation. For heavy-ball dynamics, the actual quadratic "
        "metric is positive and its pairing, Young bound and quantitative dissipation are proved.",
        "The scalar work, metric-comparison, monotonicity, force-size and coefficient inequalities "
        "appear as premises. These establish the algebra behind the appendix criteria; a general "
        "automatic derivation of all law-coupling integrals and spectral constants is not asserted."),
    "Methods": (
        "M-MFPO's concrete splitting map and finite-step robustness",
        "Force kicks, position drifts and thermostats are bounded separately, then composed "
        "for the actual OBABO map. The coupled force may be nonconservative, and the optimiser "
        "receives no thermal noise. A proved recurrence yields a finite-step perturbation bound.",
        "Assume a global Lipschitz bound for the full coupled force, a nonnegative Lipschitz "
        "constant, thermostat factor of absolute value at most one, and the displayed innovation "
        "perturbation bounds. These are pathwise robustness bounds. Their amplification factor "
        "can exceed one; they are not a Gibbs mixing or uniform-in-time convergence theorem."),
    "MomentumConsistency": (
        "M-MFPO consistency against Euler and integral dynamics",
        "The exact splitting map is compared with an Euler step using an explicit remainder "
        "budget. A norm integral estimate controls the Euler defect along a specified integral "
        "trajectory. This exposes the primitive force and trajectory estimates needed for a rate.",
        "The theorem headers specify force Lipschitz and force/momentum/noise bounds, an actual "
        "integral equation, noise matching, and a square-root trajectory-increment bound. "
        "Those particular moment/modulus and coupling estimates remain inputs to the method "
        "bound. IntegralModulus separately derives generic finite-horizon increments from "
        "actual integral equations and input estimates."),
    "HigherOrderMethod": (
        "HOL-MYPGD coefficients and endpoint-quadrature error",
        "The seven coefficients and parameter-first update follow the appendix. The optimiser "
        "force and smoothed sampler force remain independent. The exact affine response to a "
        "force perturbation and the Lipschitz endpoint quadrature defect are proved.",
        "The quadrature bound assumes nonnegative step size and a uniform Lipschitz sampler "
        "force in its spatial argument. Both updates use the same innovation triple. It compares "
        "endpoint quadrature with exact line quadrature in the same affine scheme, not with the "
        "exact SDE. Gaussian covariance validity and smoothing-target bias are separate."),
    "GeneralProcess": (
        "Constructed additive-input mean-field integral dynamics",
        "Independent time-independent globally Lipschitz observation, optimiser response and sampler maps lift "
        "to a product of a deterministic Banach coordinate and an L² random-variable coordinate. "
        "The complete field's Lipschitz constant is derived, then Picard constructs finite-horizon "
        "norm-continuous integral solutions with zero optimiser input.",
        "This construction assumes complete normed real spaces, a probability measure, the "
        "primitive global Lipschitz bounds, and a continuous L² sampler input starting at zero. "
        "It does not establish almost-sure path continuity, Brownian adaptation, an Itô integral "
        "for multiplicative noise, or all of the source's strong-SDE well-posedness assumption."),
    "Volume": (
        "Volume preservation of the frictionless kick and drift maps",
        "The deterministic splitting consists of momentum kicks and position drifts, each a "
        "shear. Their composition preserves product Haar measure for an arbitrary measurable "
        "coupled force, without requiring it to be conservative or differentiable.",
        "The measure is SFinite and translation invariant, the force measurable, and the state "
        "space has the displayed complete Hilbert/Borel/second-countability structure. Friction "
        "and random thermostat stages are excluded. ContinuousVolume separately derives the "
        "continuous Jacobian assertion from the source C¹ force and globally defined "
        "original trajectories. FlowSourceRegularity derives joint C¹ dependence."),
    "Sampling": (
        "Independent-copy empirical gradient variance",
        "The general observation map's actual finite empirical average is integrated on the "
        "finite product sampler law. The variance identity and its root mean square version "
        "give exactly the one-copy variance divided by N, and its square root divided by sqrt(N).",
        "Assume a probability sampler law, positive particle count, and an L² observation into "
        "a complete real Hilbert space with compatible Borel structure. Independence is supplied "
        "by the product law. Identifying dynamically evolved independent copies with that law "
        "and connecting the result to the interacting coupling are separate obligations."),
    "ParticleProcess": (
        "Constructed general interacting-particle integral dynamics",
        "A single shared optimiser coordinate uses the actual empirical observation average. "
        "Primitive global Lipschitz bounds give an interacting-field constant independent of "
        "positive N. Picard then constructs norm-continuous L² integral solutions.",
        "The observation, response and sampler satisfy LipschitzDynamics; N is positive; "
        "the complete interacting initial state is L²; the additive input is L²-norm continuous "
        "and starts at zero. The theorem allows arbitrary additive input, so an application "
        "must separately set its optimiser component to zero and construct independent sampler "
        "Brownian inputs. No multiplicative-noise strong-SDE claim is made."),
    "AdditiveContraction": (
        "Contraction derived from actual additive integral equations",
        "Shared additive input cancels in two actual integral equations. The fundamental "
        "theorem of calculus gives the transformed difference derivative; monotonicity then "
        "proves exponential contraction and a bounded-forcing perturbation estimate.",
        "Assume a globally Lipschitz drift on a complete real Banach space, a continuous linear "
        "map into a real Hilbert space, its displayed transformed monotonicity, continuous "
        "solution paths satisfying the integral equations, and the stated metric bounds. "
        "The forced version additionally assumes continuous forcing, its uniform transformed "
        "norm bound and matching initial states. State-dependent Itô noise is outside this result."),
    "MeanFieldContraction": (
        "Constructed mean-field solutions with joint metric contraction",
        "Picard constructs both actual general mean-field integral solutions from primitive "
        "Lipschitz observation, response and sampler maps. A joint metric monotonicity premise "
        "for their constructed field yields the exponential condition-number estimate.",
        "Assume a probability space and complete real Banach coordinates, LipschitzDynamics, "
        "time-independent primitive maps, a common continuous L² sampler input starting at zero, a continuous linear metric "
        "map into a Hilbert space, positive lower and nonnegative upper norm-comparison "
        "constants, and the stated joint drift inequality. Positive rho gives decay. No "
        "energy derivative or pre-existing solution is assumed; multiplicative noise and "
        "the optimal initial-law infimum are outside this theorem; LawContraction supplies "
        "the actual law projection and the weak-generator optimal transport bridge."),
    "FrozenCancellation": (
        "Skew Gibbs double-divergence cancellation",
        "A finite skew array has zero double sum. Symmetry of second Fréchet derivatives "
        "then proves the exact local cancellation of the skew Gibbs correction Q exp(-H).",
        "The coefficient functions and H are C², and Q is pointwise skew-symmetric. "
        "Normalisation, integration by parts, boundary conditions, nonexplosion and the "
        "stationary-PDE-to-invariant-process bridge are separate analytic requirements."),
    "HigherOrderConsistency": (
        "HOL-MYPGD consistency against its actual integral equations",
        "The exact appendix coefficients and parameter-first update are compared with the "
        "higher-order Euler map. A derived explicit budget retains coefficient, splitting "
        "and innovation errors; the reference Euler defect follows from its integral equation.",
        "Assume the displayed parameter Lipschitz force bound, force and velocity bounds, "
        "an integrable reference drift and a square-root drift modulus. Innovation mismatch "
        "with the reference final-coordinate input stays explicit. No Gaussian covariance "
        "coupling, proper prior, smoothed target or stationary law is inferred."),
    "HigherOrderRates": (
        "Explicit HOL coefficient and small-step bounds",
        "Elementary exponential remainder estimates bound all seven printed coefficient "
        "remainders by explicit multiples of h². They give a quadratic deterministic local "
        "budget and an explicit 1+Kh upper bound for the actual map amplification.",
        "Assume alpha is positive, gamma nonnegative, and 0<h≤1; force Lipschitz constants "
        "and the required force and auxiliary bounds are nonnegative where stated. These "
        "estimates quantify coefficient cancellation. Stochastic innovation-coupling and "
        "reference modulus estimates remain necessary for an overall convergence rate."),
    "HOLCoefficientAudit": (
        "Checked counterexample to exact linear-flow identification",
        "At alpha=gamma=1 the derivative of the printed mu22 coefficient is computed exactly. "
        "At h=1 its difference from mu32 equals 1−3exp(−1), which is proved nonzero.",
        "This is a concrete analytic counterexample to a necessary fundamental-matrix "
        "identity. It does not invalidate the printed numerical map or substitute a corrected "
        "covariance law; the implementation error budgets retain the actual coefficients."),
    "MethodParticles": (
        "Actual particle forces inside the two implementation maps",
        "The optimiser force is the finite empirical average and the sampler force is applied "
        "separately to each particle. Their Lipschitz constants are derived in the cloud sup norm "
        "and the two full particle method maps use zero optimiser innovations.",
        "Assume positive particle count and the separate nonnegative global joint sum-norm "
        "Lipschitz bounds for the original observation and sampler force. The whole coupled "
        "force constant is 2 max(LF,LG) in the product Banach norm. No common potential or "
        "probability independence is needed for these deterministic map estimates."),
    "NonautonomousContraction": (
        "Time-dependent drift contraction for actual integral trajectories",
        "Common additive input cancels for an arbitrary time-dependent drift. The difference "
        "derivative is derived from the two actual integral equations, then transformed joint "
        "monotonicity gives the exponential energy and norm estimates.",
        "Supply continuous trajectories, continuity of each time-dependent drift along them, "
        "the actual common-input integral equations, a continuous linear map into a Hilbert "
        "space and the uniform transformed monotonicity inequality. Existence of solutions "
        "for arbitrary time-dependent maps and state-dependent Itô noise is not proved here."),
    "BrownianProcess": (
        "Actual Brownian-coordinate inputs for general mean-field dynamics",
        "Given real pre-Brownian coordinate processes, a fixed continuous linear map produces "
        "an L²-continuous sampler input. Gaussian increment moments yield its square-root "
        "norm bound, and Picard constructs the actual general integral solution with zero "
        "optimiser input.",
        "Coordinate pre-Brownian properties are hypotheses. A probability measure, complete "
        "state spaces, primitive LipschitzDynamics and a fixed diffusion map are required for "
        "existence. The code does not infer joint coordinate independence from marginal "
        "Brownian laws, prove adapted sample-path strong SDE existence, or cover variable diffusion."),
    "IntegralModulus": (
        "Finite-horizon increments from actual integral equations",
        "Continuity bounds the drift along a continuous solution on a compact time interval. "
        "Subtracting the actual integral equations gives a drift-times-step plus input-increment "
        "bound, then a square-root modulus for steps at most one. Brownian input differences "
        "are identified with the shifted coordinate increment.",
        "Supply the actual integral equation, drift continuity, a nonnegative finite-horizon "
        "drift radius, an input square-root increment bound and a segment inside the horizon. "
        "The drift radius is proved to exist from continuity but is horizon dependent. "
        "This does not prove a uniform-in-time moment bound or a variable-diffusion Itô estimate."),
    "MomentumRates": (
        "Explicit M-MFPO small-step consistency and stability constants",
        "For the physical exponential damping and thermostat variance, coefficient estimates "
        "give a quadratic deterministic remainder plus an h sqrt(h) innovation response. "
        "The BAB amplification is bounded by 1+Kh with an explicit K.",
        "Assume a nonnegative force Lipschitz constant and friction, 0<h≤1, and nonnegative "
        "momentum, force and innovation bounds. Applying the resulting numerical rate to a "
        "stochastic process retains the exact reference-solution and innovation-coupling "
        "premises displayed in its theorem header."),
    "HOLNoise": (
        "Constructed jointly Gaussian HOL innovations and Brownian coupling",
        "The printed mu13, mu23 and mu33 response kernels are integrated on a canonical "
        "Brownian segment, together with a constant fourth kernel for its Brownian increment. "
        "The joint Gaussian law, integral Gram covariance, spatial dimension factor and "
        "independent blocks across times and spatial coordinates are proved.",
        "The construction uses the canonical Brownian source and a finite coordinate index. "
        "The fourth response is proved equal to the scaled Brownian increment. HOLCovariance "
        "separately identifies the manuscript's expanded covariance formulas. Identification "
        "of an end-to-end nonlinear SDE law remains separate."),
    "HOLNoiseRates": (
        "Derived HOL Gaussian/Brownian coupling error",
        "The actual canonical Gaussian responses are compared with their coupled Brownian "
        "Euler increment. Kernel coefficient bounds and the Brownian isometry derive an "
        "h sqrt(h) local noise discrepancy with an explicit constant and exact sqrt(d) factor.",
        "Assume alpha>0, gamma≥0 and a nonnegative segment width at most one. These "
        "results concern the constructed kernel Gaussian law, not an assumed unknown "
        "innovation error. The expanded printed covariance is identified separately in "
        "HOLCovariance; the full nonlinear reference SDE interpretation remains separate."),
    "MomentumBrownian": (
        "Actual M-MFPO Gaussian half increments and Brownian coupling",
        "Normalized actual Brownian half increments have exact sqrt(d) L² norms. With "
        "independent coordinate grid paths, the whole innovation sequence has the iid "
        "standard multivariate Gaussian law. The sum of adjacent half increments is the "
        "scaled full Brownian increment, and its thermostat mismatch is bounded explicitly.",
        "Assume a probability measure, finite spatial index, real coordinate pre-Brownian "
        "processes, positive step size and nonnegative friction. The joint Gaussian path "
        "law additionally assumes coordinate grid-path independence; marginal Brownianity "
        "alone is not substituted for it. Reference SDE existence and its moment bounds "
        "are separate from these proved innovation facts."),
    "HOLCovariance": (
        "Printed HOL covariance entries and Brownian Gram identities",
        "The six independent printed covariance entries are transcribed explicitly. "
        "Antiderivative calculations identify their kernel-product derivatives and the "
        "resulting Brownian Gram integrals in the exact statements shown below.",
        "Positive or nonzero alpha and nonnegative segment widths are imposed where "
        "needed. These covariance identities concern the printed response kernels; they "
        "do not identify those kernels with the exact full linear subsystem flow, nor "
        "prove nonlinear sampler stationarity."),
    "TargetBias": (
        "Explicit hybrid-target bias from an actual sampler coupling",
        "A strongly monotone original gradient turns a residual into a critical-point "
        "distance bound. A proved Bochner expectation comparison then gives hybrid target "
        "bias at most L epsilon/m from an actual original/surrogate L² coupling.",
        "Assume positive gradient monotonicity m, a stationary original gradient at star, "
        "a spatially Lipschitz observation, the original gradient expectation identity, "
        "zero surrogate mean observation and an actual coupling radius epsilon. The code "
        "does not derive epsilon for the Moreau model or repair the improper TV prior."),
    "GaussianMethodBounds": (
        "Finite-horizon bounds with actual Gaussian-coordinate innovations",
        "The final wrappers instantiate the two finite-horizon square-root-step estimates "
        "with actual Gaussian/Brownian innovations. M-MFPO has zero optimiser innovations "
        "and sqrt(d) noise radius; HOL uses the constructed correlated response triple and "
        "its proved explicit coupling constant. Reference premises are restricted to k<n.",
        "Assume the displayed separate Lipschitz maps on the normed/L² coordinates, actual "
        "compatible integral-reference segments and finite-horizon force/auxiliary and "
        "modulus bounds. To identify these statements with the original raw nonlinear "
        "particle implementations, their force maps must be proved equal to the pointwise "
        "L² lifts of the raw empirical and sampler forces. ParticleMethodLp proves that "
        "identification for the actual encoded finite-particle implementations and supplies "
        "their specialized final Gaussian bounds."),
    "WeakContraction": (
        "Full multiplicative-noise energy from an actual coupled generator",
        "The synchronous pair generator is computed on the weighted quadratic test with "
        "all state- and parameter-dependent diffusion columns retained. The weak forward "
        "equation and optimiser ODE derive the energy derivative, Grönwall decay and "
        "ordinary quadratic coupling-cost estimate.",
        "Assume actual marginal weak solutions and a synchronous pair forward equation, "
        "the displayed observation/test/generator integrability, quadratic separation in "
        "the pair test domain, and twisted joint monotonicity. No scalar energy inequality "
        "is assumed. Strong-SDE existence, quadratic-domain justification and equivalence "
        "with this coupled weak solution notion remain implementation obligations."),
    "LawContraction": (
        "Optimal Wasserstein law contraction and stationary uniqueness",
        "Genuine finite-second-moment couplings bound their marginal transport distance. "
        "Arbitrarily approximating couplings pass the derived generator energy bound to "
        "the exact optimiser–law product distance, with sqrt(kappa) exp(-rho t). "
        "Characteristic functions prove zero-distance separation and stationary law equality.",
        "The weak-law theorem requires a synchronous coupled weak solution with the same "
        "specified marginal trajectories for every initial coupling, and the explicit "
        "quadratic test domain. It does not assume an optimal coupling or a Wasserstein "
        "conclusion. The additive existence corollary constructs both actual integral "
        "solutions and their law bound for the selected L² initial coupling; their "
        "coupling-independent output-law identification remains separate."),
    "EmpiricalMonotonicity": (
        "Actual empirical couplings and finite-cloud joint monotonicity",
        "The finite empirical pair measure has the intended empirical marginals. "
        "Integrating joint monotonicity gives the exact finite averaged work bound, "
        "including all synchronous diffusion columns. The population-force discrepancy "
        "is isolated as its actual empirical observation fluctuation.",
        "Assume positive particle count, the general model, the positive twisted metric "
        "and its law-level joint monotonicity. Finite Dirac integrability is proved "
        "without particle independence. Dynamic independent-copy product laws and "
        "the stochastic interacting/copy generator equation are separate inputs."),
    "ParticleWeakEnergy": (
        "Interacting–copy generator on actual finite-cloud quadratic energy",
        "A genuine quadratic form on the paired optimiser/cloud state yields its first "
        "and second Fréchet derivatives. The full synchronous generator and actual weak "
        "forward equation derive the expected energy derivative, retaining precisely "
        "the population-gradient empirical fluctuation.",
        "The displayed weak forward equation, probability and moment contracts must be "
        "checked for a chosen interacting/copy stochastic implementation. The source "
        "strong-SDE-to-generator and independent-copy law identifications are not inferred "
        "merely from this generator computation."),
    "DiscreteVolume": (
        "Signed Jacobian of the original B-A-B implementation",
        "The actual kick and drift Fréchet derivatives are triangular linear shears. "
        "Their determinants are computed in a product basis, and the derivative chain "
        "rule proves determinant exactly one for the complete original interwoven B-A-B map.",
        "Assume a finite-dimensional complete real Hilbert position space and globally "
        "differentiable coupled force. The step and initial state are arbitrary. No "
        "joint potential, assumed Jacobian identity or C² force is required. Friction "
        "and stochastic thermostats are excluded, as in the source volume lemma."),
    "ParticleWeakBound": (
        "Full finite-particle empirical interaction rate from actual weak laws",
        "The exact reference-cloud product marginal gives its Var/N fluctuation. "
        "Weighted Cauchy–Schwarz and primitive optimiser response Lipschitz continuity "
        "derive the forcing term in the actual full multiplicative generator equation. "
        "The resulting regularized energy comparison gives the source empirical RMS rate.",
        "Assume the actual particle/copy weak forward equation with its quadratic test "
        "domain, positive N and rate, full joint monotonicity, zero initial energy, "
        "an almost-surely deterministic reference optimiser, the actual iid cloud marginal, "
        "L² observation and uniform variance, and the displayed residual/empirical-metric "
        "AE measurability. The interacting variables need not be independent. "
        "Strong-SDE-to-weak-equation and evolved-copy-law identification remain explicit."),
    "ContinuousVolume": (
        "Continuous Jacobian preservation from an actual C¹ joint flow",
        "The determinant derivative is derived from its multilinear form. "
        "Differentiating the actual integral ODE under a compact-set domination bound "
        "derives its spatial variational equation. The frictionless phase field has "
        "zero trace, so the fixed-time derivative has determinant exactly one.",
        "Assume finite Euclidean coordinates, a C¹ position force, an actual global "
        "joint C¹ flow Phi, its ODE at every time/state and Phi(0,x)=x. No variational "
        "or determinant equation is assumed. FlowSourceRegularity now derives joint "
        "C¹ dependence from primitive C¹ field regularity and globally existing "
        "individual trajectories. Older C²-flow lemmas remain supporting results."),
    "ParticleMethodLp": (
        "Actual raw particle force lifts and both Gaussian numerical bounds",
        "The shared random optimiser and Euclidean-encoded particle cloud have genuine "
        "pointwise L² lifts of the empirical observation and separate sampler force. "
        "Both full one-step maps are identified almost everywhere with their raw nonlinear "
        "particle implementations. Final Gaussian finite-horizon rates use those proved lifts.",
        "Assume positive particle count, a continuous linear cloud encoding with inverse, "
        "separate primitive joint Lipschitz force bounds, actual compatible integral "
        "reference segments, finite-horizon force/velocity bounds and the displayed "
        "square-root modulus. Brownian independence is explicit for M-MFPO; HOL uses "
        "the constructed canonical Gaussian source. The paper's independent isotropic "
        "particle noises use the explicit flattened Euclidean encoding; an arbitrary "
        "encoding transforms raw noise. No force-lift identification premise remains, "
        "but original-target bias and uniform-in-time mixing are separate."),
    "ProjectedCriteria": (
        "Projected primitive assumptions imply actual law-level monotonicity",
        "Coupling marginal identities turn the two force pairings into the monotone "
        "projected score work. Separate auxiliary dissipation and constant diffusion "
        "then prove full twisted joint monotonicity with an explicit certified rate.",
        "Assume pointwise U4, the separate U5 optimiser/sampler inequalities, constant "
        "diffusion, continuous linear coordinate projections with their model equalities "
        "and orthogonal norm splits, positive auxiliary coercivity and a positive residual "
        "projected rate. The relevant coupling score and auxiliary squares must be "
        "integrable. The certified rate uses min(c,mLower,vLower)/D.upper; exact "
        "generalized-eigenvalue identification is not proved."),
    "SeparatedGeometry": (
        "Weighted metric and probability quadratic-energy estimates",
        "Weighted Cauchy–Schwarz and Euclidean comparisons follow from actual symmetric "
        "positive quadratic weights. Probability-space L² estimates derive the bound "
        "on the expected square root of a nonnegative quadratic coupling energy.",
        "Assume the displayed positive lower and finite upper metric comparisons, "
        "probability normalization and actual integrability/measurability of the energy. "
        "Neither an operator-norm comparison nor a Jensen/Cauchy–Schwarz conclusion "
        "is silently supplied as a premise."),
    "HypocoerciveCriterion": (
        "Full source heavy-ball criterion with constructed metric and rate",
        "The exact source friction threshold yields explicit feasible Young, auxiliary, "
        "leakage and positive decay constants. The actual block metric is constructed. "
        "Primitive joint score monotonicity and joint Lipschitz continuity imply full "
        "law-level twisted monotonicity for the actual heavy-ball model.",
        "Assume positive friction gamma and score monotonicity r, gamma>sqrt(2)L/sqrt(r), "
        "the actual joint projected field is L-Lipschitz, and constant sampler diffusion. "
        "The optimiser and sampler spaces may differ. Auxiliary dissipation, quadratic "
        "metric positivity, rate positivity and coupling-integrability estimates are "
        "derived. The criterion does not certify these global hypotheses for experiments "
        "or establish strong-SDE existence from them."),
    "SeparatedCriteria": (
        "Primitive separate conditions imply actual joint law monotonicity",
        "Actual coupling marginal identities and the Lipschitz observation bound "
        "control the Bochner mean gradient. The primitive same-law optimiser, response, "
        "frozen-sampler, parameter-drift and diffusion-column estimates then prove "
        "full twisted joint monotonicity with the explicit source diagonal rate.",
        "Assume SeparatedAssumptions: optimiser and frozen-sampler metric dissipation, "
        "gradient-response and observation Lipschitz bounds, parameter drift bound and "
        "the full squared diffusion-column bound. The derived rate is "
        "min(rOptimizer,rSampler)-kappa Lsigma²/2-sqrt(kappa)(Lpsi LF+Lb)/2; "
        "positivity is needed for contraction. This proves the source simpler diagonal "
        "branch, not its exact two-by-two minimum-eigenvalue identification."),
    "SeparatedSchur": (
        "Full determinant small-gain criterion at the explicit spectral formula",
        "The smaller quadratic root gives the exact two-by-two quadratic-form lower "
        "bound, including degenerate and zero off-diagonal cases. The three source "
        "strict determinant conditions prove positive rate, and primitive separated "
        "conditions imply actual full law-level joint monotonicity at that rate.",
        "Assume SeparatedAssumptions and the displayed two positive diagonal conditions "
        "and determinant inequality for positivity. The rate is the explicit formula "
        "(a+b-sqrt((a-b)²+c²))/2, where the off-diagonal entries are -c/2. "
        "The algebraic lower bound and positive rate are proved; SmallGainSpectrum "
        "additionally identifies this formula with the actual matrix minimum eigenvalue."),
    "ParameterBound": (
        "Actual parameter L² bound from stationary and particle weak laws",
        "The target constant weak solution is built from frozen sampler stationarity, "
        "zero mean observation and the optimiser fixed point. Its optimal transport "
        "relaxation combines with the actual generator particle energy and an L² "
        "triangle estimate for the random optimiser and parameter projection.",
        "The mean-field and particle/copy weak equations, quadratic test domains, "
        "same-marginal synchronous realizations for every initial target coupling, "
        "actual iid reference marginal, response/variance and measurability contracts, "
        "zero initial particle energy and one-Lipschitz parameter projection are "
        "explicit. Strong-SDE realization and original-target model identification "
        "remain implementation obligations."),
    "SmallGainSpectrum": (
        "Exact minimum eigenvalue and positive definiteness of the source matrix",
        "The explicit smaller-root rate is identified with the actual minimum of "
        "the two eigenvalues of the symmetric source matrix using its trace and "
        "determinant. The three strict source conditions then prove matrix positive "
        "definiteness, in addition to the actual law-level monotonicity certificate.",
        "The matrix is [[a,-c/2],[-c/2,b]]. Its eigenvalue identity holds for every "
        "real a,b,c, including repeated eigenvalues. Positive definiteness assumes "
        "a>0, b>0 and c²<4ab; those quantities are instantiated by the source "
        "metric and primitive separated constants in SeparatedSchur."),
    "NumericsTarget": (
        "Actual particle numerical errors combined with a stationary target",
        "L² triangle and coordinate projection estimates combine the two actual "
        "Gaussian particle implementation bounds with the proved weak-process "
        "stationary parameter bound. Compatible parameter-law equality transfers "
        "the reference RMS bound across the numerical and weak-law probability spaces.",
        "The raw-particle Lipschitz/encoding and finite-horizon integral/moment/modulus "
        "contracts remain explicit, together with the full weak-generator stationary "
        "target data and the displayed reference-parameter law equality. No final "
        "numerical error or target-rate premise substitutes for those proofs. "
        "Original/surrogate target shifts require an actual coupling-radius bias "
        "estimate; TV prior repair and the model-specific radius remain separate."),
    "GeneralizedSpectrum": (
        "Exact generalized minimum-eigenvalue quadratic comparison",
        "Spectral diagonalization proves the lower bound at the actual finite "
        "minimum eigenvalue. Positive definiteness of D and K gives positivity "
        "of the whitened matrix D^(-1/2) K D^(-1/2), and congruence converts its "
        "spectral estimate into K-rho D positive semidefinite.",
        "Assume finite nonempty real matrix coordinates and genuine positive-definite "
        "D and K. The positive square root, its invertibility and the identity "
        "between inverse square root and square root of the inverse are proved. "
        "The generalized minimum is the actual smallest eigenvalue, not a supplied "
        "scalar quadratic comparison constant."),
    "CanonicalProjectedCriterion": (
        "The full canonical source projected-field spectral criterion",
        "Literal parameter/auxiliary and position/auxiliary Euclidean coordinates "
        "construct the actual matrix metric. SPD source D and auxiliary matrices "
        "and positive residual c construct both block K matrices, their positivity "
        "and all coordinate identities. The exact generalized spectral source rate "
        "then proves full joint law monotonicity.",
        "Assume the four source matrices are SPD, literal source coordinate projections, "
        "U4 score monotonicity, the two separate U5 inequalities, nonnegative beta, "
        "c=beta r-AOpt-ASam>0, constant diffusion and the explicit finite coupling "
        "integrability contract. Parameter and position dimensions are nonempty; "
        "auxiliary dimensions may be zero. No metric coercivity, coordinate-form "
        "identity, K positivity or final spectral comparison is supplied as a premise."),
    "AdditiveJointBridge": (
        "Source joint law monotonicity implies constructed additive contraction",
        "The actual common-space L² sampler pair gives a genuine joint pushforward "
        "law. Its marginals, second moments, Bochner observation and weighted work "
        "identities derive lifted drift dissipation from source A3. Picard then "
        "constructs both integral solutions with the exact Euclidean L² metric rate.",
        "Assume primitive globally Lipschitz independent observation, response and "
        "sampler maps compatible with Model, autonomous optimiser response, constant "
        "diffusion columns, a common continuous L² sampler input starting at zero, "
        "and source twisted joint monotonicity. No lifted drift or energy inequality "
        "is assumed. The common input is not automatically identified with Model's "
        "diffusion: a samplerBrownianInput K implementation must separately match "
        "the columns sigma_i=sqrt(2) K e_i; AdditiveDiffusion constructs a normalized K that proves this identity for any finite constant column family. Strong-SDE adaptation and realization-"
        "independent output laws remain separate."),
    "ProductTransport": (
        "Exact Wasserstein distance of deterministic-optimiser product laws",
        "The actual law is identified with the literal Dirac optimiser tensor "
        "sampler measure in the Euclidean WithLp 2 product. Lifted and projected "
        "genuine couplings and their infima prove its quadratic transport distance "
        "equals sqrt(optimiser separation²+sampler W2²). Full weak product-law "
        "contraction follows from the derived generator law theorem.",
        "Assume complete real Hilbert coordinates with Borel and second-countable "
        "structure and probability sampler laws with finite second moments. "
        "The dynamic theorem retains the actual coupled weak generator, quadratic "
        "test domain and same-marginal synchronous realization for every initial "
        "coupling. No product-distance identity or transport conclusion is assumed."),
    "LpPullback": (
        "Actual mean-field dynamics and laws under probability-space pullback",
        "A measure-preserving map pulls back L² variables by a genuine linear "
        "isometry. Primitive lifted maps, Bochner expectations, the complete field "
        "and actual integral equations commute with that pullback. The output "
        "sampler law is proved unchanged by the actual change of variables.",
        "Assume the displayed measure-preserving map, probability/finite measures "
        "where required, complete real Banach coordinates and primitive Lipschitz "
        "maps. The optimiser coordinate is unchanged and the common input is "
        "actually pulled back. No equality of forces or output laws is supplied "
        "as a hypothesis; stochastic adaptation remains separate."),
    "AdditiveWeakRealization": (
        "Constructed global additive processes and actual quadratic weak couplings",
        "Finite Picard solutions are glued by proved uniqueness to give a global "
        "norm-continuous integral process. The optimiser ODE, actual marginal laws, "
        "second moments and observation integrability follow. Common-input "
        "cancellation derives the actual pair quadratic forward equation.",
        "Assume primitive global Lipschitz maps, a common continuous sampler input "
        "starting at zero and explicit autonomous/constant-diffusion model "
        "compatibility. Marginal tests are exactly empty and the pair domain is "
        "the singleton quadratic separation test: this does not prove arbitrary "
        "marginal Itô/Fokker–Planck equations. AdditiveDiffusion constructs the "
        "correctly scaled model Brownian input; adaptation and richer "
        "generator domains remain separate."),
    "IntegralStationarity": (
        "Stationarity from actual sampler integral equations and uniqueness",
        "The complete parameter- and state-dependent diffusion remains in an "
        "actual pathwise sampler integral equation. The frozen invariant sampler "
        "and optimiser fixed point form a genuine constant-optimiser integral "
        "solution. Same-driver pathwise uniqueness proves its full output law "
        "is literally the deterministic optimiser tensor frozen sampler law.",
        "The stochastic integral operator J and admissible process class C are "
        "supplied explicitly. No Itô implementation is constructed here. "
        "Assume actual frozen invariant "
        "trajectory and law, finite second moment, observation integrability, "
        "zero mean gradient, optimiser fixed point and same-driver pathwise "
        "uniqueness of the displayed integral equations. Intended Itô/adapted "
        "process-class instantiation remains separate."),
    "GlobalODE": (
        "Constructed actual ODE trajectories for every real time",
        "Forward and reverse global Picard integral solutions are glued at "
        "zero. The fundamental theorem of calculus gives their actual ODE "
        "derivatives, including the matched two-sided derivative at zero. "
        "Thus every initial state has a genuinely all-real-time trajectory.",
        "Assume a complete real Banach state space and a globally Lipschitz "
        "primitive field. Neither trajectory existence nor regularity of the "
        "selector in the initial state is a premise. Joint C¹ dependence is "
        "subsequently derived by FlowDifferentiability for C¹ fields."),
    "GlobalIntegral": (
        "Constructed global Banach additive-input integral solutions",
        "Finite Picard solutions for an arbitrary globally Lipschitz Banach "
        "vector field are glued by proved common-input uniqueness. The result "
        "constructs an actual global norm-continuous solution with the specified "
        "initial value and additive integral equation on every nonnegative time.",
        "Assume a complete real Banach state space, a globally Lipschitz field, "
        "an initial state and continuous additive input starting at zero. A "
        "global solution is a conclusion. Negative times are continuously "
        "extended by the initial value; the equation is asserted for t≥0."),
    "FlowSourceRegularity": (
        "Source C¹ flow regularity and continuous volume preservation",
        "A compact-orbit cutoff, the constructed global cutoff trajectories "
        "and compact-open containment prove local equality of the original "
        "flow with a genuinely C¹ localized flow. Thus primitive C¹ field "
        "regularity and actual globally defined trajectories imply joint C¹ "
        "flow dependence. The actual phase determinant is then one.",
        "Assume a finite-dimensional real complete normed state, a C¹ primitive "
        "field, the actual all-time ODE and identity initial map. Joint flow "
        "regularity, variational equations, a global Lipschitz bound and "
        "determinant preservation are conclusions, not premises. The phase "
        "force is arbitrary and may be nonconservative."),
    "FlowDifferentiability": (
        "Joint C¹ flow dependence derived from primitive globally Lipschitz fields",
        "The actual path-space Picard map is C¹, and its contraction gives "
        "the invertibility needed by the Banach implicit function theorem. "
        "Uniqueness derives the semigroup identity; scaled time and iteration "
        "extend short-time dependence to all times. The phase-flow determinant "
        "is then one without supplying any regularity of the flow.",
        "Assume a C¹ globally Lipschitz primitive field, a complete proper real "
        "normed state space, actual all-time ODE trajectories and the identity "
        "initial map. Continuity in initial data, a variational equation and "
        "joint flow differentiability are conclusions. Removing global "
        "Lipschitz regularity is discharged for finite-dimensional source fields "
        "by FlowSourceRegularity through actual compact-orbit localization."),
    "FlowLocalization": (
        "C¹ globally Lipschitz localization near a compact orbit",
        "A smooth compact cutoff leaves an arbitrary C¹ field unchanged on an "
        "open neighbourhood of a given compact set. Its actual derivative has "
        "compact support, which proves a global Lipschitz constant for the "
        "localized field rather than assuming one for the original field.",
        "Assume a finite-dimensional real normed domain, a normed real target, "
        "C¹ field and compact set. This is a localization helper; it does not "
        "itself prove joint C¹ dependence; FlowSourceRegularity composes it with "
        "constructed cutoff trajectories to derive the full source result."),
    "AdditiveCanonicalRealization": (
        "Constructed additive law trajectories for every initial coupling",
        "Each marginal process is constructed once on initial-law times noise "
        "space. Measure-preserving projections pull both onto the actual "
        "initial-coupling times noise extension, preserving their output laws. "
        "The exact initial pair law and actual quadratic weak equation give "
        "optimal optimiser–Wasserstein contraction without a realization premise.",
        "Assume primitive global Lipschitz maps, autonomous response and constant "
        "diffusion compatibility, probability noise space, finite-second-moment "
        "initial laws and common continuous sampler input starting at zero. "
        "Source A3 supplies the joint metric monotonicity. Marginal tests are "
        "empty and the pair domain is exactly the quadratic singleton. The normalized "
        "model Brownian input has proved coefficient matching; adaptation, richer "
        "marginal Itô equations and frozen-target invariance remain separate."),
    "AdditiveDiffusion": (
        "Constructed constant diffusion operator with exact Brownian scaling",
        "A finite family of arbitrary diffusion columns gives an actual "
        "continuous linear map from Euclidean noise. Its normalized map "
        "exactly matches the sqrt(2)-scaled Brownian input constructor, so "
        "every constant-diffusion compatible model has the required columns.",
        "Assume finite noise coordinates and the displayed real Hilbert "
        "sampler structure. The Brownian identity uses the supplied coordinate "
        "pre-Brownian inputs. No matrix-matching identity is a premise for "
        "the constructed normalized operator. General multiplicative Itô "
        "integration and coordinate independence remain separate."),
    "IndependentCopies": (
        "Actual iid reference cloud and independent complete trajectories",
        "One complete seed per copy is sampled under a finite product law. "
        "Applying the same actual measurable one-copy variable proves the "
        "fixed-time cloud has the exact iid marginal law. The same construction "
        "proves independence of entire coordinate trajectories and genuine "
        "isometric L² pullbacks along the seed projections.",
        "Assume a probability seed law, finite copy index and actual measurable "
        "one-copy variables or measurable trajectory evaluations. Interacting "
        "particles are not asserted independent. The construction must still "
        "be identified with the intended reference equations and shared-driver "
        "interacting/copy system before discharging that full process contract."),
    "AdditiveStationaryTarget": (
        "Actual frozen invariance constructs the additive stationary target",
        "The frozen trajectory supplies actual continuous L² sampler dynamics, "
        "its integral equation and its constant output law. Zero mean gradient "
        "and the optimiser fixed point derive the complete constant-optimiser "
        "solution. Primitive uniqueness proves canonical target stationarity "
        "and constructs every initial-coupling target realizer.",
        "Assume primitive globally Lipschitz autonomous additive model maps, "
        "constant diffusion compatibility, the actual frozen invariant "
        "trajectory, zero gradient, optimiser fixed point, positive joint "
        "monotonicity and one-Lipschitz parameter projection. The marginal test "
        "family is empty, but actual frozen invariance is a substantive input; "
        "it is not inferred from vacuous generator stationarity."),
    "ParticleAdditiveWeakRealization": (
        "Constructed global additive interacting/copy particle processes",
        "Actual iid seed pullbacks of the one-copy integral process build the "
        "reference cloud. Picard constructs the shared-optimiser interacting "
        "process with the true empirical force and common input. Its actual "
        "quadratic weak generator, iid reference marginal, deterministic "
        "reference optimiser and zero initial energy are all derived.",
        "Assume positive N, primitive globally Lipschitz autonomous additive "
        "maps compatible with the model, a global one-copy integral reference, "
        "continuous sampler input from zero and the uniform observation "
        "variance. The final ParticleParameterApproximation is constructed, "
        "not supplied. Its test domain is the particle quadratic singleton; "
        "richer Itô equations and general multiplicative input remain separate."),
    "ParameterLawTransfer": (
        "Derived numerical parameter-law identities from actual L² packing",
        "Actual shared paired pushforwards and L² coercion identities prove "
        "the parameter marginal law and its exact RMS norm. Concrete momentum "
        "and HOL packings retain every particle and shared optimiser in genuine "
        "WithLp 2 Hilbert coordinates, with square integrability and pointwise "
        "identification proved. Their parameter laws are exactly phase theta.",
        "Assume the displayed Borel normed coordinates and Lipschitz parameter "
        "projection where used. No final law-compatibility equality is a "
        "premise: both laws use the same actual variables and packing. This "
        "does not identify two independently supplied process constructions; "
        "their actual reference equations must still be linked."),
    "QuadraticMartingale": (
        "Expected quadratic derivative from actual martingale structure",
        "The residual is the actual L² process minus its initial value and "
        "Bochner drift integral. A standard martingale representative yields "
        "weighted orthogonality through conditional expectation. Exact forward "
        "and backward quadratic expansions and the increment isometry derive "
        "the expected energy derivative without a forward-equation premise.",
        "Assume norm-continuous L² state, drift and finite diffusion columns, "
        "an adapted state, a standard martingale representative of the actual "
        "residual, symmetric continuous metric weight and its explicit weighted "
        "increment isometry. Constructing a multiplicative stochastic integral "
        "and proving that isometry for it remain analytic obligations."),
    "ImplementationDynamics": (
        "Both proposed methods as actual general Hilbert-state models",
        "Independent primitive Lipschitz forces construct the actual M-MFPO "
        "heavy-ball optimiser/underdamped sampler and the HOL three-coordinate "
        "sampler model. All primitive mean-field Lipschitz data and model "
        "compatibility are proved, with genuine Hilbert products. The original "
        "raw finite-empirical drifts intertwine exactly with the model drifts.",
        "Assume complete real Hilbert optimiser/sampler coordinates, separate "
        "global sum-Lipschitz bounds for F and G and the displayed friction "
        "coefficients. Finite constant diffusion columns are supplied. No "
        "common potential, equal optimiser/sampler dimensions, unrelated model "
        "compatibility equality or final error bound is a premise."),
    "GeneralMartingaleRealization": (
        "Actual full state-dependent diffusion quadratic weak realization",
        "Actual L² drift and diffusion columns realize the general model, "
        "and the drift residual is a standard martingale. Adaptation and the "
        "synchronous weighted increment isometry derive the actual quadratic "
        "pair forward equation. The source joint criterion then proves energy "
        "decay without a supplied energy or weak forward equation.",
        "Assume continuous L² state, drift and diffusion, their pointwise model "
        "identities, actual optimiser ODE, observation integrability, adapted "
        "state, martingale residual and SynchronousIsometry. Diffusion may "
        "depend on parameter and state. Marginal tests are empty and the pair "
        "domain the quadratic singleton. Constructing the intended stochastic "
        "integral/isometry and richer marginal Itô domains remains separate."),
    "ConstructedParameterBound": (
        "Actual source parameter bound for constructed additive particles",
        "The canonical one-copy process, independent reference cloud and actual "
        "interacting process are constructed from primitive maps. Actual frozen "
        "invariance constructs target data and all target couplings. Parameter "
        "law transfer is proved internally, giving the exact source parameter "
        "bound without any final process-data or compatibility premise.",
        "Assume autonomous globally Lipschitz additive model maps, primitive "
        "model compatibility, actual frozen invariant trajectory, positive "
        "source joint criterion, one-Lipschitz parameter projection and uniform "
        "observation variance. For the concrete methods, ImplementationDynamics "
        "constructs compatibility from F/G. The general multiplicative Itô "
        "realization and numerical reference identification remain separate."),
    "ParticleNoiseSpace": (
        "Actual independent particle seeds preserve flattened canonical noise",
        "Each particle seed pairs its initial sampler state with an independent "
        "canonical Brownian source. Projecting initial states away and flattening "
        "particle/spatial noise indices preserves the entire canonical source "
        "measure. The actual initial cloud has the iid product marginal and is "
        "independent of the entire flattened Brownian source; their full "
        "joint product law is derived.",
        "Assume a probability initial sampler law and the displayed finite "
        "particle index. No final noise-law identity is supplied. This is a "
        "measure-preserving full-source construction; numerical reference "
        "equations and their moments/moduli remain separate."),
    "HOLPullback": (
        "HOL Gaussian rates on actual random-initial particle/noise spaces",
        "A measure-preserving pullback transports the entire four-kernel "
        "innovation array and coupled Brownian increments. Isometric L² "
        "pullback preserves the proved noise budget and finite-horizon HOL "
        "bound, with the actual raw-particle force lifts on the same space.",
        "The generic theorem assumes a measure-preserving noise projection; "
        "ParticleNoiseSpace constructs it on actual independent initial/noise "
        "particle seeds. Positive step at most one, alpha>0, gamma≥0, primitive "
        "forces, compatible original integral segments and finite-horizon "
        "moments/modulus remain explicit. No Gaussian noise-error premise is "
        "supplied, and the full temporal/spatial joint law is derived."),
    'ImplementationCoordinates': (
        'Actual raw and Hilbert implementation state equivalences',
        'Explicit continuous linear equivalences and their inverses identify every shared optimiser and sampler auxiliary coordinate of the momentum and HOL implementations with the full actual particle model.',
        'Assume complete real Hilbert optimiser and sampler spaces and finite particle count. These are coordinate identities, without any supplied equality of laws, drifts or error estimates; actual lifted dynamics are identified in ImplementationLpCoordinates.',
    ),
    'ImplementationLpCoordinates': (
        'Same-sample L² implementation coordinates and exact integral transfer',
        'Continuous linear maps split actual full particle L² states into the original implementation coordinates. Pointwise force, complete drift, parameter and Bochner integral equations are identified exactly on the same sample space.',
        'Assume the primitive separate force bounds and explicit invertible particle encoding. The actual source integral equation and continuity are supplied; coordinate and force-lift identities are proved. Numerical segmentation and moment estimates are discharged in the method construction modules.',
    ),
    'ParticleBrownianInput': (
        'Actual copied Brownian inputs equal flattened block diffusion',
        'Independent complete initial/noise seeds produce the actual copied sampler inputs. Their full L² equality with an explicit flattened particle/spatial block-column Brownian input is proved, with exactly zero optimiser diffusion.',
        'Assume the finite constant sampler diffusion map and probability initial sampler law. The common complete Brownian source, flattening and full input identity are constructed; no final covariance, noise-law or matching equality is a premise. This is an additive input construction.',
    ),
    'GlobalMeshRegularity': (
        'Derived finite-horizon state, drift and square-root modulus constants',
        'Compactness of the actual continuous integral trajectory derives its state and drift radii. The actual Brownian input increment bound and global Lipschitz drift then derive one square-root modulus uniformly for all mesh intervals of length at most one in the fixed horizon.',
        'Assume an actual norm-continuous L² integral trajectory, primitive globally Lipschitz drift and fixed linear Brownian input from the supplied coordinate pre-Brownian laws. No moment radius or increment-modulus estimate is supplied; no uniform-in-time bound follows.',
    ),
    'MethodBrownianMatching': (
        'Exact physical Brownian and implementation innovation identities',
        'The kinetic two-half Gaussian innovation sum equals the physical full-step Brownian input. The fourth HOL response kernel equals the physical final-auxiliary Brownian input after actual whole-source pullback.',
        'The identities use actual Brownian coordinates and physical coefficient signs. HOL uses an actual measure-preserving canonical-noise projection, constructed by ParticleNoiseSpace for independent initial/noise seeds. No covariance or innovation-matching premise substitutes for the proved L² equalities.',
    ),
    'MethodDiffusionCoordinates': (
        'Physical diffusion equals the original method input in L² coordinates',
        'The actual source model block diffusion is transformed through the proved implementation coordinate maps. This yields exactly momentum-only kinetic forcing and final-auxiliary-only HOL forcing on the same random initial/noise space.',
        'Assume the literal flattened Euclidean particle encoding, complete real Hilbert optimiser coordinate and actual coordinate pre-Brownian inputs. The encoding condition is needed for independent isotropic original particle noise. No final diffusion or input matching identity is supplied.',
    ),
    'MethodIntegralSegments': (
        'Original integral equations give exact numerical reference segments',
        'Subtracting two actual global integral equations and shifting the Bochner integral gives the exact step equation. The physical Brownian input increment is identified with the implementation reference innovation for both methods.',
        'Assume the actual global integral equation and continuous drift. The exact segment equation and Gaussian-input matching are conclusions. Moment and modulus estimates are derived separately from the actual source process by the method reference constructors.',
    ),
    'MomentumIntegralConstruction': (
        'Actual kinetic references and mesh-uniform regularity are constructed',
        'The actual global interacting source integral process is transported to its original momentum/position coordinates. Compactness and Brownian increments derive all finite-horizon force, momentum and square-root modulus constants, and exact segmentation constructs compatible references on every admissible mesh.',
        'Assume primitive separate force data, actual continuous full interacting integral process, its physical Brownian equation, canonical Euclidean particle encoding and nonnegative friction. No supplied reference, force/momentum bound, modulus or output coordinate identity remains. FullyConstructedMomentum also constructs the source process itself.',
    ),
    'HigherOrderIntegralReference': (
        'Actual HOL references and mesh-uniform regularity are constructed',
        'The actual full interacting HOL integral process is transported into its original optimiser,x,u,v L² coordinates. State and drift compactness and Brownian increments derive mesh-uniform auxiliary, force and drift-modulus bounds. Exact segmentation and actual innovation identities construct every reference.',
        'Assume primitive separate force data, actual continuous full interacting integral process and its physical Brownian integral equation, canonical Euclidean cloud encoding, alpha>0 and gamma≥0. No supplied reference equation, node moment, drift modulus, coordinate or innovation matching remains. FullyConstructedHigherOrder constructs that actual source process too.',
    ),
    'ConstructedNumerics': (
        'Numerical target estimates for constructed additive particle processes',
        'Actual frozen invariance and primitive maps construct the continuous target, every target coupling and interacting/copy process. Gaussian numerical error bounds combine with its exact source parameter estimate on the actual independent initial/noise particle space.',
        'These intermediate wrappers retain an explicit L² identity between the supplied integral reference and actual interacting parameter coordinate. FullyConstructedMomentum and FullyConstructedHigherOrder subsequently derive the reference, all mesh-uniform regularity and that coordinate identity internally; the general multiplicative strong-SDE bridge remains open.',
    ),
    'FullyConstructedHigherOrder': (
        'HOL-MYPGD target bound with its process and reference constructed',
        'Primitive independent forces construct the actual physical HOL model and global interacting particles. All original L² coordinates, physical diffusion, Gaussian coupling, mesh-uniform moments and drift modulus, exact integral references and initial equality are derived. The final parameter bound combines discretization, relaxation and particle terms.',
        'Assume separate global joint Lipschitz bounds for F and G, canonical Euclidean cloud encoding, alpha>0, gamma≥0, positive particle count and source A3 rate, initial and frozen target P₂ laws, an actual frozen invariant sampler trajectory, zero target mean gradient and uniform observation variance. No reference, process package, moment/modulus or law-compatibility conclusion is a premise. The optional original-target corollary requires actual coupled target observations with explicit radius and positive gradient monotonicity. This is a finite-horizon additive integral theorem, without a general multiplicative Itô claim.',
    ),
    'FullyConstructedMomentum': (
        'M-MFPO target bound with its process and reference constructed',
        'Primitive independent forces construct the actual heavy-ball/underdamped model and interacting particle dynamics. Original same-sample L² coordinates, physical Brownian increments, Gaussian innovations and mesh-uniform moments/moduli derive the complete reference and zero initial discretization error.',
        'Assume the displayed separate global joint Lipschitz bounds for F and G, canonical Euclidean cloud encoding, nonnegative friction, positive source A3 rate, P₂ initial/target laws, actual frozen invariant sampler, zero target mean observation and uniform variance. The target optimiser momentum is zero and its fixed point is derived. No supplied reference, moment/modulus, final law equality or weak-process package remains. The bound concerns fixed finite horizons and constructed additive integral dynamics.',
    ),
    'EmpiricalMeasurability': (
        'Actual empirical-cloud Wasserstein statistic is measurable',
        'Finite equality-pattern strata handle duplicate particle locations. On each stratum every genuine empirical coupling pulls back to a fixed finite index-coupling space, and its transport cost is continuous in the two clouds. The actual coupling infimum is measurable, giving the empirical particle metric statistic and its AE measurability for every joint law.',
        'Assume positive finite particle count and the displayed Borel second-countable real Hilbert coordinates. Neither an optimal coupling, a Wasserstein triangle estimate nor measurability of the desired statistic is supplied. The helper discharges the empirical-metric measurability contract in ParticleWeakBound.',
    ),
    'PredictableIsometry': (
        'Actual past-dependent Gaussian sums are martingales and isometries',
        'On a genuine iid Gaussian path source, arbitrary measurable coefficients depend on the complete strict past. Fresh-past independence, conditional centering and Gaussian second moments derive the actual predictable-sum martingale, weighted isometry and L² distance identity.',
        'Assume finite noise coordinates, square-integrable coefficient columns and their measurable finite-past dependence. The symmetric continuous metric weight is arbitrary. This is a finite unit-grid construction; continuous stochastic integration is not claimed here.',
    ),
    'BrownianGridIsometry': (
        'Actual predictable Brownian sums on compatible time grids',
        'All deterministic time grids use the same actual scalar Brownian path and its full natural past. Adapted square-integrable random coefficients yield actual martingale sums and exact weighted isometry. Arbitrary compatible subdivision preserves the original sum pathwise.',
        'Assume actual scalar pre-Brownian laws, measurable evaluations, monotone deterministic grids and coefficients measurable in the original Brownian past with finite second moments. Coefficient independence is derived from the increment/past law, not assumed. Continuous completion and general diffusion membership are separate.',
    ),
    'BrownianVectorFiltration': (
        'Joint future-past independence with an independent initial state',
        'Independent coordinate pairs are rearranged to prove full vector future-past independence on the actual canonical Brownian source. Pairing an independent random initial state gives the actual natural initial/noise filtration and increment independence from its complete past.',
        'Assume finite spatial coordinates and the displayed probability/measurability structure. The canonical product construction supplies independence; no final vector independence identity is a premise. These are filtration foundations, not a solution existence or general Itô theorem.',
    ),
    'TimeGridEnergy': (
        'Literal time-L² energy and exact deterministic grid refinement',
        'Indicator-function columns embed finite left-step coefficients into the genuine L² time space. Disjoint interval inner products give the exact sum of interval lengths times coefficient norms squared. Arbitrary compatible subdivision preserves the embedded coefficient itself.',
        'Assume a complete real Hilbert coefficient space and monotone finite deterministic time grids. These are actual L² time functions and exact refinement identities. No stochastic integral or density theorem is asserted.',
    ),
    'GridIntegralCompletion': (
        'Actual L² stochastic integral on the represented step-function domain',
        'Actual adapted Brownian sums on compatible refining grids satisfy an exact cross-grid distance identity. Cauchy convergence of the literal time-L² coefficients constructs an actual L² stochastic-integral limit and proves its norm and isometry. Dyadic grids are explicitly constructed.',
        'IntegralDomain consists precisely of time-L² limits represented by the actual adapted step approximations in the signature. Scalar pre-Brownian laws and measurable evaluations are explicit. Density, membership of arbitrary continuous diffusion processes, timewise martingale consistency and a full state-dependent SDE are not claimed by this completion alone.',
    ),
    'MartingaleL2Limit': (
        'Actual adapted martingale representatives of timewise L² limits',
        'Hilbert conditional projection is a continuous map on actual L² variables. Its martingale identity passes to every timewise L² limit; conditional expectations provide adapted representatives of the limit and prove their standard martingale property.',
        'Assume a filtration, actual approximating square-integrable martingales and timewise L² convergence. No limiting adaptedness or conditional-expectation identity is supplied as a premise. Constructing a consistent stochastic-integral process from these limits remains a separate step.',
    ),
    'FilteredBrownian': (
        'Primitive filtered vector Brownian drivers and actual predictable sums',
        'An arbitrary finite coordinate Brownian driver retains its actual filtration, coordinate adaptation, spatial increment independence and complete future-vector independence from the full past. These primitive properties derive finite predictable-vector martingales and weighted isometry with pathwise deterministic refinement.',
        'Driver contains only Brownian laws, filtration, adaptation and independence. Square-integrable random coefficient columns are measurable at the actual left endpoint. No stochastic-integral, final martingale or isometry conclusion is a Driver field. CanonicalBrownianDriver constructs these properties for the actual canonical initial/noise source.',
    ),
    'CanonicalBrownianDriver': (
        'Constructed full-vector Brownian Driver with random initial state',
        'The canonical product of a sampler initial law and full vector Brownian source supplies the genuine natural filtration of the initial state and all spatial pasts. Coordinate adaptation, spatial increment independence and whole-vector future/past independence are proved, constructing every primitive Driver field.',
        'Assume a probability initial-state law, finite noise coordinates and the displayed Borel second-countable normed initial space. No future-past independence, adaptation or noise-law identity is supplied as a premise. This is a driver construction; the SDE solution and coefficient integrability remain separate.',
    ),
    'FilteredBrownianPullback': (
        'Constructed Brownian drivers on actual independent particle seeds',
        'A measure-preserving source map pulls back the full filtration and derives every primitive vector Brownian Driver property. The proved joint initial-cloud/whole-noise product map then constructs the actual flattened particle Driver, whose coordinate process is exactly the original per-particle Brownian coordinate.',
        'The generic pullback uses a genuine measure-preserving map and an actual Driver; no output-law or adaptedness conclusion is assumed. The particle specialization derives that map from ParticleNoiseSpace and requires only the stated probability initial law and finite coordinates. Its filtration includes the entire initial cloud and all joint noise pasts.',
    ),
    'BrownianWeightedCompletion': (
        'Scalar completed Brownian integrals retain actual weighted isometry',
        'The finite weighted moment identity passes to the actual L² stochastic-integral limit for every bounded symmetric metric weight. Actual represented-domain subtraction gives integral subtraction, and literal interval cuts identify increment energies.',
        'The scalar construction uses the actual adapted-step approximation domain and explicitly identified deterministic interval integrands. Stochastic weighted isometry is proved, not supplied. Membership of arbitrary diffusion processes and a full SDE are not concluded by this scalar theorem alone.',
    ),
    'FilteredIntegralCompletion': (
        'Actual full-vector stochastic integral on represented time-L² columns',
        'The actual Driver predictable sums complete in L² from compatible refining grids of genuine adapted random coefficient columns. The column space is the real Hilbert finite L² product; exact cross-grid distance gives the actual integral, convergence and isometry.',
        'IntegralDomain consists of actual time-L² limits of adapted step columns on the stated compatible grids. Primitive Driver properties replace any assumed stochastic-integral isometry. FilteredContinuousIntegrands derives domain membership for continuous adapted columns rather than asking the application to supply an approximation.',
    ),
    'FilteredWeightedCompletion': (
        'Full-vector completed integrals have derived weighted increment isometry',
        'A genuine bounded symmetric weight acts columnwise on the finite time-L² Hilbert space. Finite moment formulas pass to completed integrals; actual domain subtraction and literal interval cuts derive stochastic integral subtraction and weighted increment moments.',
        'The generic theorem displays represented-domain membership and exact deterministic interval integrand identities. No stochastic moment/isometry conclusion is assumed. FilteredContinuousIntegrands instantiates both membership and those identities for actual continuous adapted L² diffusion columns.',
    ),
    'TimeGridContinuity': (
        'Dyadic time-L² convergence derived for actual continuous integrands',
        'Actual deterministic dyadic left-step functions converge pointwise away from interval endpoints. Compactness supplies the finite horizon radius and dominated convergence gives literal time-L² convergence, including deterministic interval masks.',
        'Assume the displayed measurable integrand, almost-everywhere continuity and finite horizon bound; the continuous-masked corollary derives the bound from compactness. No grid-approximation or stochastic-isometry premise is supplied. These are deterministic coefficient-density facts, without an SDE existence assertion.',
    ),
    'FilteredContinuousIntegrands': (
        'Continuous adapted diffusion columns belong to the actual integral domain',
        'Compactness and proved dyadic time-L² convergence construct the actual domain element for continuous adapted finite L² columns, including all deterministic interval cuts. Its value is the literal time-cut column function; the completed weighted increment moment follows from the finite Brownian construction.',
        'Assume a primitive actual Driver, norm-continuous finite L² column paths and their current-past AE measurability. Domain membership, grid convergence, a horizon radius and stochastic increment isometry are derived rather than supplied. The minimal source A1 coefficient regularity and actual solution identification remain separate.',
    ),
    'FilteredBrownianMartingale': (
        'Actual stopped predictable Brownian sums are continuous-time martingales',
        'A single stopped Brownian increment multiplied by a genuine left-endpoint adapted random column has the exact conditional centering identities before and after that endpoint. Finite stopped sums therefore form actual continuous-time martingales; the limit wrapper uses actual L² convergence.',
        'Assume primitive actual Driver laws/filtration/independence, adapted square-integrable coefficients and the displayed deterministic grid. Neither noise martingale nor limiting martingale identities are supplied. FilteredIntegralMartingale derives the needed convergence for actual completed continuous integrands.',
    ),
    'TimeGridCut': (
        'Exact finite deterministic split grids for stopped integrands',
        'Clamping a deterministic grid at a cut and selecting its actual nonempty intervals gives a monotone finite split grid. The literal embedded step function is exactly the deterministic time restriction, with the corresponding interval and refinement identities proved.',
        'Assume only the displayed finite deterministic monotone grids and cut coordinates. This is an exact identity of actual time-L² embeddings, with no approximation, stochastic isometry or final martingale premise.',
    ),
    'FilteredIntegralMartingale': (
        'Actual completed continuous-integrand vector Itô martingales',
        'For an actual Driver and continuous adapted finite L² columns, literal stopped-step approximations converge to the constructed time-cut integral. The actual finite stopped sums are martingales, and continuous conditional projection constructs an adapted standard martingale representative of the completed integral process.',
        'The integrand is norm-continuous and current-past AE measurable; the process is stopped after the fixed horizon. No limiting-martingale, stochastic-convergence or isometry premise is supplied. The source general SDE and minimal A1/localization transfer still require their own proof.',
    ),
    'IntegralAdaptation': (
        'Adaptation derived from actual global Lipschitz integral equations',
        'Picard is constructed inside each complete invariant past-measurable L² subspace. Actual common-input uniqueness identifies that trajectory with the selected original solution, proving current-past measurability. This applies to pointwise lifted particle drifts and the complete nonlinear deterministic-optimiser/L²-sampler mean-field field. Actual Driver Brownian inputs are proved adapted.',
        'Assume primitive globally Lipschitz maps, actual continuous integral equations and current-past measurable initial variable and additive input. No solution adaptedness conclusion is assumed and no conditional projection is claimed to commute with a nonlinear drift. A strongly adapted representative is constructed with a.e. equality at each time; simultaneous pathwise continuity is not established by this theorem alone.',
    ),
    'IntegralQuadraticEnergy': (
        'Actual martingale energy balance with time-integrable coefficients',
        'Exact expected quadratic increments are proved from the actual drift residual martingale and weighted diffusion-increment isometry. Bochner L¹-time L² drift and time-L² diffusion suffice for the energy balance and almost-everywhere integral Grönwall estimate, without continuous coefficients or an assumed energy derivative.',
        'The residual martingale and actual stochastic increment isometry remain explicit in this general interface; the latter is separately constructed for arbitrary time-L² adapted finite columns. The generic decay theorem takes a coefficient dissipation inequality; transferring source A3 and minimal source A1 into these coefficient identities is separate, without a strong-SDE equivalence claim.',
    ),
    'ConstructedAdaptation': (
        'Actual selected mean-field and particle processes are adapted',
        'The original canonical initial variable and physical Brownian input are identified with the actual canonical initial/noise Driver. The same argument identifies complete particle initial clouds and packed Brownian input. Actual integral equations and primitive Lipschitz maps then derive current-past measurability of the selected canonical mean-field and interacting particle states.',
        'Assume the displayed primitive globally Lipschitz additive model and P₂ initial law. No initial/input measurability, solution-adaptedness or final law identity is a premise. The particle theorem applies to the actual constructed realization structure via its original equation and initial identity. Strongly adapted representatives have per-time a.e. equality; simultaneous sample-path continuity requires a further version argument.',
    ),
    'FilteredIntegralPullback': (
        'Constructed stochastic integrals commute with actual source pullback',
        'Actual coefficient composition under a measure-preserving map transports the adapted domain, finite Brownian sums, time-L² column embedding and L² limits. The actual constructed integral is proved equal to the pulled-back original integral under the fully transported Driver and filtration.',
        'Assume a genuine measure-preserving source map and actual Driver. No final integral identity, limiting stochastic isometry or output-law equality is supplied. Together with the constructed canonical/particle Drivers, this supports law coherence across actual initial-coupling probability spaces; it does not itself construct a general SDE solution.',
    ),
    'FilteredIntegralContinuity': (
        'The constructed vector Itô integral is L²-time continuous',
        'The exact completed-integral increment norm equals the actual coefficient time-energy. Compactness of a continuous adapted finite L² column path supplies a horizon bound, yielding an explicit square-root increment estimate and actual L² time continuity of the stopped integral.',
        'Assume an actual primitive Driver and continuous adapted finite L² columns. No stochastic-input continuity or increment modulus is supplied. This proves L² time continuity, without asserting a simultaneous almost-sure continuous sample-path version or the full source A1 SDE realization.',
    ),
    'IntegralModelContraction': (
        'Source A3 contracts actual integral trajectories with integrable coefficients',
        'Actual optimiser integral equations, time-L¹ L² drift, time-L² diffusion columns and a genuine residual martingale give the energy balance. Literal pointwise model coefficient identities and actual joint-law pullback derive dissipation from source A3, proving energy, joint-cost RMS and marginal Wasserstein contraction.',
        'The trajectory contains original integral equations and coefficient realization, not an energy bound. Actual stochastic weighted increment isometry remains explicit at this general interface; continuous adapted coefficients have a separately constructed realization. No continuous coefficient or pointwise optimiser derivative is needed. General source A1 realization and all-initial-coupling law coherence remain separate.',
    ),
    "Check": (
        "Logical audit of the formal results",
        "This file imports the development and prints the logical axioms used by selected results.",
        "An axiom audit reports logical dependencies, while analytic premises remain visible in "
        "the theorem signatures. Absence of sorryAx does not remove a theorem's hypotheses."),
    "PBGSO": (
        "PBGSO library entry point",
        "This module imports the general framework and its quantitative and implementation proofs.",
        "Importing the library assembles the proved statements. Each theorem retains the explicit "
        "analytic and algebraic premises shown on its supporting page."),
}



# Completed analytic extensions after the previous documentation checkpoint.
MODULES.update({'FilteredIntegralEnlargement': ('Actual completed integrals agree under valid filtration '
                                 'enlargement',
                                 'The same primitive Brownian process may be viewed in two valid '
                                 'Driver filtrations ordered by inclusion. Actual finite '
                                 'predictable sums agree and their literal coefficient values are '
                                 'unchanged. Completion then proves equality of the computed '
                                 'integrals, including continuous-input processes.',
                                 'Both filtrations must satisfy the genuine Driver future-past '
                                 'independence contract. Arbitrary anticipating enlargement is not '
                                 'asserted. Neither an integral-equality nor a final output-law '
                                 'premise is supplied.'),
 'CoupledBrownianFiltration': ('Canonical arbitrary-initial-coupling Brownian alignment',
                               'Every actual initial coupling carries a common full-vector '
                               'Brownian source. Both pulled-back marginal natural filtrations are '
                               'contained in the genuine full joint initial/past filtration. '
                               'Computed marginal stochastic integrals agree on this common '
                               'filtration and retain their original marginal laws.',
                               'No independence between the two initial coordinates is required. '
                               'The probability initial laws, actual coupling and finite noise '
                               'coordinates are explicit. Full Driver properties, integral '
                               'commutation and output-law identities are derived.'),
 'PastAverages': ('Actual time-L² translation averages',
                  'The actual measure-preserving translation action is Bochner averaged in the '
                  'genuine time-L² space. FTC proves convergence to every original integrand, '
                  'while norm contraction and Lipschitz continuity are derived. Literal pointwise '
                  'moving means of locally integrable curves are continuous.',
                  'No original time continuity is assumed. Linking the time-L² average to its '
                  'pointwise moving mean is a separate Fubini identity supplied by '
                  'LpIntegralSections; adaptedness is supplied by AdaptedPastAverages.'),
 'AdaptedPastAverages': ('Past Bochner averaging preserves actual adaptation',
                         'Actual conditional L² projection fixes all past-measurable variables. '
                         'Commuting this continuous linear projection with the past Bochner '
                         'integral proves current-past measurability of moving means, without '
                         'commuting it through a nonlinear coefficient.',
                         'The curve is locally Bochner integrable and its AE-time '
                         'past-measurability condition is explicit. Actual pointwise adaptation '
                         'and zero values before time zero derive that condition. No density or '
                         'stochastic isometry conclusion is assumed.'),
 'FilteredPastAverages': ('Continuous adapted approximants for general diffusion columns',
                          'Finite Hilbert columns of actual L² variables are averaged over the '
                          'past. Each pointwise moving mean is proved continuous and adapted. It '
                          'therefore gives a concrete represented integral-domain entry and a '
                          'literal closed-domain element.',
                          'The original columns need only time-L² membership and AE-time past '
                          'adaptation. The exact identity with the time-L² translation average is '
                          'supplied by LpIntegralSections; PredictableStepDensity then proves '
                          'convergence and general domain membership.'),
 'ClosedIsometricExtension': ('Computed isometric extension to a literal closed range',
                              'A map on actual finite represented inputs is well defined because '
                              'equal inputs have zero output distance. Its actual uniformly '
                              'continuous extension to the literal closure is constructed and '
                              'proved isometric, preserving represented values and approximation '
                              'limits.',
                              'The primitive finite-data distance identity and completeness of the '
                              'output are explicit. No norm, continuity or isometry property is '
                              'imposed on the completed map as an extra conclusion premise.'),
 'ClosedStepIntegration': ('Actual Itô integral on the closed predictable-step domain',
                           'The domain is literally the closure of actual finite adapted '
                           'Brownian-step coefficient embeddings in time-L². The computed '
                           'isometric extension gives its actual stochastic integral, derived '
                           'finite approximating sequences and weighted moments. It agrees with '
                           'the earlier refining-grid construction on that domain.',
                           'A domain member is a genuine closure member, not a field containing a '
                           'final error bound or stochastic isometry. PredictableStepDensity '
                           'proves membership from raw time-L² adapted columns; full source SDE '
                           'existence remains separate.'),
 'PredictableStepDensity': ('Density derived for arbitrary time-L² adapted columns',
                            'Actual past averages converge in time-L² and have continuous adapted '
                            'pointwise representatives. Their deterministic Brownian-step '
                            'approximations and the Fubini identification place every '
                            'finite-horizon time cut of the original columns in the literal closed '
                            'predictable-step domain.',
                            'Assume only actual time-L² columns and AE-time past adaptation. No '
                            'time continuity, supplied approximation, integral isometry or '
                            'martingale identity is a premise. This is integrand density, not SDE '
                            'well-posedness.'),
 'ClosedDomainCuts': ('Literal closed predictable-step domains are stable under interval cuts',
                      'Finite adapted step coefficients have actual adapted interval restrictions. '
                      'General predictable density and continuous mask approximation then pass the '
                      'restriction through the literal closure, constructing closedCutDomain with '
                      'its exact time-cut value.',
                      'No extra adaptedness, time continuity or approximation sequence is required '
                      'of the closed-domain member. These are deterministic domain identities used '
                      'to construct one consistent stochastic integral process.'),
 'ClosedStepAlgebra': ('Actual closed-domain addition and integral subtraction',
                       'Finite adapted steps are placed on a common exact refinement. Their '
                       'literal coefficient embeddings and actual Brownian sums give genuine '
                       'addition and subtraction identities. Closure and continuity prove domain '
                       'subtraction and subtraction of the computed integral.',
                       'No linearity conclusion is assumed of the completion. The initial Drivers '
                       'and finite coefficient square-integrability/adaptation provide the '
                       'primitive stochastic data.'),
 'ClosedIntegralMartingale': ('Computed closed-domain integrals form actual martingales',
                              'Actual finite stopped predictable sums converge on compatible '
                              'refinements to the computed integral of every literal closed-domain '
                              'member. Conditional L² projection gives an adapted '
                              'square-integrable standard martingale representative, with exact '
                              'per-time equality to the computed L² values.',
                              'No limiting martingale, convergence or stochastic-isometry premise '
                              'is supplied. This covers general closed predictable-step '
                              'integrands; sample-path continuity is not inferred solely from L² '
                              'convergence.'),
 'ClosedIntegralEnergy': ('General closed-domain integral increments and L² continuity',
                          'Literal interval cuts and proved subtraction give the exact weighted '
                          'second moment of every increment of the computed integral. Time-cut '
                          'continuity derives its actual L²-time continuity and zero initial '
                          'value. PredictableIntegral instantiates these facts for arbitrary '
                          'time-L² adapted columns.',
                          'The bounded weight is selfadjoint and the actual primitive Driver is '
                          'explicit. No diffusion time continuity, stochastic increment isometry '
                          'or integral-process continuity is assumed. Simultaneous almost-sure '
                          'continuous paths are separate.'),
 'ClosedIntegralTransport': ('Computed closed-domain integrals commute with source transport',
                             'Actual finite adapted coefficients pull back under '
                             'measure-preserving maps and enlarge to valid larger Driver '
                             'filtrations, preserving both literal time-L² inputs and Brownian '
                             'sums. Closure and actual norm-limit uniqueness prove transport of '
                             'the computed integrals and all observation-time cuts.',
                             'The source map must be genuinely measure preserving and the enlarged '
                             'filtration must itself form a valid Driver. No final integral '
                             'identity, output-law equality or extra approximation premise is '
                             'supplied.'),
 'PredictableCurveIntegral': ('Actual Itô integration of raw time-L² adapted diffusion curves',
                              'A raw finite-column curve with finite horizon time-L² norm and '
                              'actual current-past measurability enters the literal closed domain '
                              'through the proved density theorem. Its computed real-time integral '
                              'has a standard martingale representative, derived L² continuity, '
                              'zero initial value, weighted increment moments and subtraction.',
                              'No time continuity of diffusion columns is required. The original '
                              'actual Driver and time-integrability/adaptation assumptions remain '
                              'explicit. The integral is constructed; primitive source SDE '
                              'existence and simultaneous sample paths remain separate.'),
 'IntegralForcedEnergy': ('Forced-energy comparison from actual integral balances',
                          'An absolutely continuous Grönwall argument and a regularized '
                          'square-root chain rule derive the exact forced bound sqrt(E(T)) ≤ '
                          '(c/rho)(1−exp(−rho T)) from an actual integral energy balance and '
                          'AE-time dissipation. Compact-range Lipschitz regularity justifies the '
                          'square-root limit.',
                          'Positive rho, nonnegative forcing, the explicit integrability and '
                          'integral-equation premises are required. No pointwise energy derivative '
                          'or pre-existing final energy estimate is assumed.'),
 'IntegralParticleBound': ('Full particle interaction bound with time-integrable coefficients',
                           'The actual particle/copy drift and diffusion, joint-law pushforwards '
                           'and source A3 derive expected energy balance and the exact source '
                           'empirical RMS interaction bound. The reference-cloud iid marginal '
                           'supplies Var/N forcing; empirical-statistic measurability is proved.',
                           'The actual drift is Bochner L¹-time L² and diffusion time-L². At this '
                           'general interface the residual standard martingale and normalized '
                           'stochastic increment isometry are explicit. No test-domain, final '
                           'energy, residual-measurability or continuous-coefficient premise is '
                           'required. A constructed-integral wrapper discharges the stochastic '
                           'interface separately.'),
 'ConstructedItoModel': ('General model contraction from the computed continuous-column Itô '
                         'integral',
                         'Original optimiser/sampler integral equations driven by the actually '
                         'computed Brownian integral construct the full model integral trajectory. '
                         'State continuity, the residual martingale, synchronous weighted '
                         'isometry, source A3 energy and actual law contraction are derived.',
                         'The drift is Bochner L¹-time L² and the finite diffusion columns are '
                         'continuous adapted L² variables in this module. No stochastic-isometry '
                         'or weak-generator conclusion is supplied. The intended minimal source A1 '
                         'process class and localization remain separate.'),
 'ConstructedItoPullback': ('Actual model equations survive source pullback and valid enlargement',
                            'The computed Brownian integral commutes with a genuine '
                            'measure-preserving source map and a valid larger full Driver '
                            'filtration. Original model equations, coefficient realizations, '
                            'adaptation and actual output laws transfer together, producing '
                            'genuine coupled model trajectories.',
                            'The raw coefficient/equation data remain the primitive inputs. No '
                            'integral identity, output-law compatibility or final coupling-energy '
                            'premise is supplied. The continuous-column module is an explicit '
                            'realization subclass.'),
 'ConstructedItoLaw': ('Actual state-dependent model law contraction from canonical data',
                       'Two actual canonical model trajectories are pulled to every initial '
                       'coupling with a common full initial/noise filtration. Original equations, '
                       'fixed marginal output laws, stochastic martingale/isometry identities and '
                       'energy decay then pass to the actual Wasserstein infimum, giving the '
                       'source condition-number contraction factor.',
                       'This module takes actual canonical integral-equation data with Bochner '
                       'L¹-time L² drift and continuous adapted L² diffusion. No all-couplings '
                       'realizer, output-law equality or stochastic-interface premise remains. '
                       'Identifying every source A1 strong solution with such data is still '
                       'separate.'),
 'LpIntegralSections': ('Actual Bochner L² integration agrees with joint pathwise integration',
                        'Finite-set integration is constructed as a bounded Hilbert linear map. '
                        'Fubini and equality of all finite-set integrals identify the actual L² '
                        'Bochner integral with the spatial section integral of every known joint '
                        'realization. Local product integrability is derived internally.',
                        'Assume a Bochner L¹ family of L² variables, a jointly AE strongly '
                        'measurable realization and AE-time exact sections. No '
                        'product-integrability premise is needed. LpJointRepresentative constructs '
                        'such a joint realization on finite time/probability spaces.'),
 'LpJointRepresentative': ('Constructed joint representatives of arbitrary L¹-time L² variables',
                           'Actual finite-valued time families have literal strongly measurable '
                           'joint representatives. A proved L²-to-L¹ bound makes their product-L¹ '
                           'lifts Cauchy. Completion, product-AE subsequences and uniqueness in '
                           'measure construct a genuine jointly strongly measurable '
                           'product-integrable representative with exact AE-time L² sections.',
                           'The time measure is finite, the spatial measure a probability, and the '
                           'output a complete real Hilbert space. No measurable global L² '
                           'evaluation map or joint representative is assumed. Every actual '
                           'time-set Bochner integral has its proved section identity.'),
 'LpContinuousVersion': ('One simultaneous continuous original additive path version',
                         'A constructed joint drift representative has literal continuous pathwise '
                         'primitives. Adding the actual raw input gives one jointly strongly '
                         'measurable process version. Fubini transfers the original nonlinear '
                         'drift equation on one full-measure spatial event for every time in the '
                         'horizon, preserving every actual L² marginal.',
                         'The raw additive input must be jointly strongly measurable, represent '
                         'the actual L² input at each horizon time, and have almost-sure '
                         'continuous paths. The L¹-time L² drift and actual integral equation are '
                         'explicit; nonlinear drift continuity and its original L² realization are '
                         'used. A pre-Brownian Driver alone does not supply sample-path '
                         'continuity.'),
 'MartingaleMaximalL2': ('Derived weak-L² martingale maximal inequality',
                         'Conditional Jensen proves that the actual squared norm of a '
                         'square-integrable martingale is a submartingale. The finite-grid Doob '
                         'maximal inequality then bounds every monotone observation grid by its '
                         'actual terminal second moment.',
                         'The martingale, filtration and ordered finite observation grid are '
                         'explicit. No maximal inequality is assumed. This is a finite-grid '
                         'foundation; a simultaneous continuous modification is not asserted.'),
 'AdditiveContinuousVersion': ('Continuous original mean-field sampler paths from actual integral '
                               'solutions',
                               'The primitive global sampler bounds give a genuine jointly '
                               'Lipschitz sampler field. The actual complete mean-field integral '
                               'equation projects to its sampler equation and derives all L¹-time '
                               'drift and nonlinear realization conditions. A constructed joint '
                               'representative then gives one jointly strongly measurable version '
                               'with actual initial value, continuous paths and the literal '
                               'original sampler equation for every horizon time on one '
                               'full-measure event.',
                               'The actual raw additive input must be jointly strongly measurable, '
                               'have the stated per-time L² identity and almost-sure continuous '
                               'paths. No joint drift or final path equation is supplied. '
                               'Combining the exact per-time version identity with proved L² '
                               'adaptation gives AE current-past measurability; strict '
                               'measurability in an uncompleted natural filtration and a Brownian '
                               'continuous modification are not asserted here.'),
 'ConstructedItoParticle': ('Source particle error from the actually computed continuous-column '
                            'integral',
                            'Actual raw particle/copy model drift and diffusion identities are '
                            'driven by the completed finite-column Brownian integral. Its '
                            'martingale, weighted stochastic isometry, original energy balance, '
                            'reference-only Var/N fluctuation and source A3 yield the exact '
                            'empirical RMS interaction floor. The actual parameter-to-target '
                            'triangle is also proved.',
                            'Data requires Bochner L¹-time L² drift and continuous adapted L² '
                            'diffusion in this module. Only the reference cloud has the iid law, '
                            'with uniform observation variance and deterministic reference '
                            'optimiser explicit. No martingale, stochastic-isometry, '
                            'weak-test-domain or final error premise remains; source minimal '
                            'A1/localization is separate.'),
 'ConstructedPredictableModel': ('General model contraction with merely time-L² adapted diffusion',
                                 'Original optimiser and sampler integral equations driven by the '
                                 'computed predictable Brownian integral construct the actual '
                                 'model integral trajectory. Density, martingale, exact weighted '
                                 'stochastic isometry, state L² continuity, source A3 energy and '
                                 'genuine law contraction are derived for arbitrary parameter- and '
                                 'state-dependent diffusion.',
                                 'Diffusion columns need only actual horizon time-L² membership '
                                 'and current-past AE adaptation; drift is Bochner L¹-time L². No '
                                 'diffusion time continuity, stochastic isometry, residual '
                                 'martingale or final energy premise is supplied. Realizing the '
                                 "paper's entire minimal A1 strong-solution class, including "
                                 'localization and simultaneous sample paths, remains separate.'),
 'PredictableIntegralTransport': ('Actual raw predictable-curve integrals retain canonical laws',
                                  'The literal horizon column function commutes with '
                                  'measure-preserving source pullback. The actually computed raw '
                                  'predictable-curve integral also commutes with pullback and '
                                  'valid full Driver filtration enlargement at every observation '
                                  'time.',
                                  'Only actual horizon time-L² membership and AE current-past '
                                  'measurability are required of the raw diffusion columns. No '
                                  'integral equality, noise law or fixed marginal output identity '
                                  'is a conclusion premise. Enlarged filtrations must satisfy the '
                                  'genuine Driver contract.'),
 'MartingaleCountableMaximal': ('Derived weak-L² bounds for countably many observation times',
                                'Any finite set of earlier observations is internally ordered and '
                                'the terminal observation appended. The finite-grid Doob bound '
                                'passes through countable unions, giving the same actual '
                                'terminal-second-moment bound for every countable family of '
                                'earlier observation times.',
                                'No observation ordering, process time continuity or maximal '
                                'inequality is assumed. This is a countable-observation estimate; '
                                'extending a martingale to simultaneous continuous sample paths '
                                'requires a separate construction.'),
 'ConstructedPredictablePullback': ('Original predictable model equations commute with '
                                    'common-source transport',
                                    'Actual merely time-L² adapted model coefficients and their '
                                    'computed Brownian integral pull back under genuine '
                                    'measure-preserving maps and enlarge to valid common Driver '
                                    'filtrations. Every original model equation, adaptation '
                                    'property and actual marginal output law is preserved.',
                                    'No coefficient time continuity, stochastic moment identity, '
                                    'final integral identity or output-law compatibility is a '
                                    'premise. The true Driver and original time-integrable model '
                                    'data remain explicit.'),
 'ConstructedPredictableLaw': ('Optimal actual model law contraction with merely time-L² diffusion',
                               'Two actual canonical model trajectories with arbitrary parameter- '
                               'and state-dependent adapted diffusion are aligned on every genuine '
                               'initial coupling. Computed-integral transport, full joint '
                               'filtration, energy balance and the actual Wasserstein infimum '
                               'prove the source metric contraction factor with the true '
                               'initial-law distance.',
                               'Drift is Bochner L¹-time L² and diffusion is adapted time-L²; '
                               'actual original integral equations, coefficient realizations, '
                               'initial variables and source A3 are explicit. No time continuity '
                               'of diffusion, martingale, isometry, output-law equality, '
                               'all-couplings realization or final energy premise remains. '
                               "Identifying the paper's entire minimal A1 strong-solution class is "
                               'still separate.'),
 'ConstructedPredictableParticle': ('Source particle interaction bound from computed time-L² Itô '
                                    'noise',
                                    'Original raw full particle/copy drift and diffusion are '
                                    'driven by the actually computed predictable Brownian '
                                    'integral. Its martingale/isometry, actual joint-law energy, '
                                    'reference-only iid Var/N forcing and source A3 derive the '
                                    'exact source empirical RMS interaction floor. An actual-law '
                                    'parameter triangle is proved internally.',
                                    'Only Bochner L¹-time L² drift and adapted time-L² packed '
                                    'diffusion are required; no coefficient continuity, residual '
                                    'martingale, stochastic isometry, energy bound or '
                                    'weak-test-domain premise is supplied. The reference iid '
                                    'marginal, deterministic reference optimiser, synchronous '
                                    'initial condition and uniform observation variance are '
                                    'explicit. Minimal source A1 realization/localization remains '
                                    'separate.'),
 'MartingaleUniformLimit': ('Actual uniformly convergent martingale series foundations',
                            'A Borel–Cantelli argument constructs a literal telescoping-series '
                            'limit uniformly in time from summable dense-observation increment '
                            'tail bounds and actual continuous approximant paths. Actual finite '
                            'stopped predictable Brownian sums have continuous paths when the '
                            'coordinate Driver paths do.',
                            'Dense observation set, actual continuity of approximants and the '
                            'displayed summable tail budget are explicit. No uniform convergence '
                            'or limiting path continuity is assumed. Coordinate pre-Brownian laws '
                            'alone do not supply continuous coordinate paths.')})


# Additional constructed Brownian versions and localization foundations.
MODULES.update({'BrownianFourthMoment': ('Actual Gaussian fourth moments and increment tails',
                          'The actual fourth moment of the standard Gaussian supplies a finite '
                          'positive-or-zero constant. Scaling derives the exact centered '
                          'variance-v fourth moment and actual pre-Brownian increment tail bounds.',
                          'Assume a probability source and actual scalar pre-Brownian laws. The '
                          'constant is its actual integral, not an assumed moment bound; its exact '
                          'numerical value is unnecessary.'),
 'BrownianTimeContinuity': ('Brownian time continuity in probability and limit identification',
                            'Actual fourth-moment tails prove convergence in measure along every '
                            'convergent deterministic time sequence. Strict past dyadic samples '
                            'therefore identify any actual almost-sure limit with the original '
                            'fixed-time variable.',
                            'Only pre-Brownian laws and convergence of deterministic nonnegative '
                            'times are assumed. No sample-path continuity or supplied modification '
                            'identity is required.'),
 'BrownianDyadicProbability': ('Dyadic Brownian tail summability and continuous polygon limits',
                               'Markov on the actual sum of adjacent fourth powers gives a '
                               'geometric dyadic-grid tail budget. Borel-Cantelli and '
                               'deterministic interpolation construct an almost-sure uniform '
                               'continuous polygon limit on every scaled finite horizon.',
                               'A probability source and genuine scalar pre-Brownian laws suffice. '
                               'No grid independence, path continuity, tail or convergence '
                               'conclusion is assumed.'),
 'DyadicInterpolation': ('Literal dyadic polygon interpolation',
                         'Finite continuous hat sums reproduce endpoint interpolation and bound '
                         'consecutive polygon levels by actual fine-grid adjacent increments.',
                         'These are deterministic finite identities and norm bounds on the unit '
                         'window. The original sampled curve need not be continuous.'),
 'DyadicInterpolationLimit': ('Uniform continuous limits of actual polygons',
                              'Completeness of continuous maps turns summable eventual '
                              'adjacent-increment bounds into actual uniform convergence of the '
                              'dyadic polygons.',
                              'Assume the displayed summable deterministic increment budget; the '
                              'Brownian probability module derives it almost surely from genuine '
                              'Gaussian laws.'),
 'DyadicPastSamples': ('Strict past dyadic times and polygon comparison',
                       'Floored dyadic times stay in the past, approach the current time and '
                       'differ from actual polygon values by the adjacent-grid increment budget, '
                       'including the right endpoint.',
                       'Nonnegative times and positive grid size are explicit. No adaptation or '
                       'continuity premise enters these deterministic estimates.'),
 'DyadicPastLimit': ('A measurable past-series candidate for continuous limits',
                     'The unconditional telescoping series of successive strict-past samples '
                     'converges to the actual uniform polygon limit under the derived summable '
                     'increment budget.',
                     'The candidate is defined on all sample points. Continuity is proved where '
                     'the eventual adjacency bounds hold; measurability and adaptation are '
                     'supplied by its actual past evaluations.'),
 'AdaptedBrownianWindow': ('Continuous adapted Brownian modification on one horizon',
                           'The actual strict-past series defines an adapted candidate. Gaussian '
                           'dyadic estimates prove its continuous paths and convergence in '
                           'probability identifies it with every original fixed-time Brownian '
                           'variable.',
                           'Assume genuine pre-Brownian laws, positive finite horizon and, for '
                           'adaptation, the original process adapted to its stated filtration. No '
                           'completed-filtration or raw path-continuity assumption is needed.'),
 'ContinuousVersionGlue': ('Countable-horizon continuous modification glue',
                           'Countably many fixed-time dyadic identities and path continuity prove '
                           'simultaneous overlap equality. The explicit ceiling-horizon selector '
                           'then gives one global continuous version and retains strict '
                           'adaptation.',
                           'The generic input consists of actual continuous horizon versions and '
                           'fixed-time almost-everywhere identities. Neither global overlap nor '
                           'global continuity is assumed.'),
 'AdaptedBrownianModification': ('An actual globally continuous adapted Brownian modification',
                                 'The explicit countable-horizon past-series process has the '
                                 'original finite-dimensional Brownian laws and actual continuous '
                                 'paths, and is strictly adapted to the original filtration.',
                                 'Assume a probability source, actual pre-Brownian laws and '
                                 'original adaptation where requested. The construction proves the '
                                 'continuous modification; original raw paths are not claimed '
                                 'continuous.'),
 'ContinuousBrownianDriver': ('Continuous modifications preserving the full Brownian Driver',
                              'Coordinate past-series modifications retain the exact original '
                              'filtration. Fixed-time identities derive all spatial increment '
                              'independence and full future-past independence, yielding a valid '
                              'continuous Driver.',
                              'The input is an actual finite-coordinate Driver. No path '
                              'regularity, independence or output-integral identity for the '
                              'modified process is assumed.'),
 'ContinuousMartingaleCompletion': ('Continuous martingale versions from actual maximal bounds',
                                    'A terminal-L2 Cauchy family of actual continuous-path '
                                    'martingales yields an internally selected fast subsequence '
                                    'with almost-sure uniform continuous limit, through the proved '
                                    'maximal inequality and Borel-Cantelli.',
                                    'Actual approximating martingales, terminal L2 convergence and '
                                    'their continuous paths are explicit. Uniform convergence and '
                                    'continuity of the limit are conclusions.'),
 'ClosedIntegralContinuousVersion': ('Continuous versions of actual completed stochastic integrals',
                                     'Actual stopped-grid martingales and the maximal completion '
                                     'theorem construct continuous all-time and jointly measurable '
                                     'finite-window versions of the computed integral.',
                                     'This intermediate theorem assumes coordinate Brownian path '
                                     'continuity. ContinuousBrownianDriver now derives a valid '
                                     'modification with that property; integral modification '
                                     'invariance preserves the original computed noise.'),
 'FilteredIntegralModification': ('Computed integrals are invariant under Brownian modification',
                                  'Fixed-time almost-everywhere equality of valid Driver '
                                  'coordinates proves equality of actual finite sums, '
                                  'closed-domain integrals, observation cuts and raw '
                                  'predictable-curve integrals.',
                                  'Both Drivers must satisfy their primitive laws and independence '
                                  'contracts. The target filtration may enlarge the original; raw '
                                  'path equality and stochastic-output equality are not assumed.'),
 'ConstructedStationarity': ('Stationary laws for the actual computed predictable integral',
                             'An actual frozen invariant sampler constructs the constant-optimizer '
                             'model Data and, under same-initial uniqueness, its literal Dirac '
                             'optimizer tensor sampler stationary law.',
                             'The frozen process obeys the computed original integral equation in '
                             'the time-L1(L2) drift and adapted time-L2 diffusion class. Actual '
                             'invariant law, observation integrability, zero mean gradient and '
                             'optimizer fixed point are explicit. Minimal source A1 realization '
                             'remains separate.'),
 'ConstructedUniqueness': ('Actual same-initial uniqueness from source A3',
                           'The constructed difference integral and source joint monotonicity '
                           'imply equality of both optimizer states and sampler L2 variables for '
                           'equal initial data.',
                           'The original computed-integral Data class, measurable raw '
                           'drift/diffusion and actual twisted joint monotonicity are explicit. '
                           'Positive contraction rate is unnecessary for uniqueness itself; '
                           'minimal-A1 localization is not proved here.'),
 'LpMeasurableContinuousVersion': ('Simultaneous pathwise integral equations for measurable drift',
                                   'Joint L1 representatives and Fubini construct one continuous '
                                   'sampler version satisfying the original nonlinear drift '
                                   'integral equation simultaneously at all horizon times, '
                                   'requiring only joint strong measurability of the field.',
                                   'Actual original L2 equations, time-L1(L2) drift, and a joint '
                                   'continuous raw input version are explicit. Pathwise drift '
                                   'integrability is derived; the selected sampler is asserted AE '
                                   'adapted per time rather than strictly adapted on every sample '
                                   'point.'),
 'ConstructedSamplerPaths': ('Computed model sampler paths under continuous drift',
                             'Actual completed Brownian noise and joint drift regularity construct '
                             'simultaneous continuous original-equation sampler paths, exact '
                             'fixed-time L2 variables and derived AE adaptation.',
                             'This supporting theorem assumes coordinate Brownian continuity and '
                             'continuous joint original drift. Later measurable-drift and '
                             'modified-Driver corollaries weaken these inputs.'),
 'ConstructedMeasurableSamplerPaths': ('Computed original sampler paths for measurable drift',
                                       'The actual completed noise and Fubini path construction '
                                       'give one jointly measurable continuous sampler version, '
                                       'with the original nonlinear drift equation on one '
                                       'probability-one horizon event.',
                                       'Actual computed-integral Data, coordinate Brownian '
                                       'continuity and horizon joint strong measurability of the '
                                       'original drift are explicit. Pathwise drift integrability '
                                       'and per-time AE adaptation are proved.'),
 'ConstructedSamplerModification': ('Original sampler equations under a continuous Driver '
                                    'modification',
                                    'A valid fixed-time Brownian modification preserves literal '
                                    'model states and actual computed noise. Continuous paths of '
                                    'that modified Driver then give a simultaneous continuous '
                                    'sampler realization of the original equations.',
                                    'Fixed-time coordinate equality and valid filtration '
                                    'enlargement are explicit in this intermediate API. '
                                    'ContinuousBrownianDriver constructs these inputs; no original '
                                    'raw Brownian path-continuity assertion is made.'),
 'ConstructedContinuousSampler': ('Continuous original sampler paths with Brownian modification '
                                  'derived',
                                  'The continuous Driver is constructed internally and its actual '
                                  'integral invariance proves one jointly measurable continuous '
                                  'sampler/noise version satisfying the original drift equation on '
                                  'a single horizon event.',
                                  'The input is actual original computed-integral Data with '
                                  'time-L1(L2) drift and adapted time-L2 diffusion, plus strong '
                                  'measurability of the original joint drift on the horizon. '
                                  'Brownian continuity, noise matching, pathwise drift '
                                  'integrability and per-time AE adaptation are derived. This does '
                                  'not identify the whole minimal source A1 class.'),
 'StoppingSteps': ('Actual finite-grid stopped Brownian integrals',
                   'Genuine stopping events produce predictable masked coefficients, exact stopped '
                   'finite sums, actual martingales and completed finite-grid random-time '
                   'realization.',
                   'The finite deterministic grid and genuine stopping measurability are explicit. '
                   'This module alone does not assert arbitrary bounded stopping.'),
 'StoppedIntegralMask': ('Exact completed finite-grid stopped integral and energy',
                         'The original column coefficients multiplied by actual stopping '
                         'indicators lie in the completed domain, and their computed integral '
                         'equals the original noise at the finite-grid stopping time, with exact '
                         'weighted energy.',
                         'An actual finite-grid stopping index and valid Driver are explicit. '
                         'Domain membership, coefficient identification and computed-noise '
                         'equality are derived.'),
 'DyadicStopping': ('Actual bounded stopping times approximated by finite grids',
                    'Ceiling dyadic stops obey genuine grid stopping events, decrease to the '
                    'original bounded stopping time with explicit mesh error, and preserve '
                    'interval-indicator limits even at atoms.',
                    'A bounded nonnegative stopping time and its primitive stopping events are '
                    'inputs. No random-time stochastic identity is assumed.'),
 'StoppingLpLimit': ('Stopped coefficient domains and actual stochastic limits',
                     'Nested dominated convergence identifies literal original columns times the '
                     'bounded-stop indicator as a predictable completed-domain member, and proves '
                     'L2 convergence of the actual dyadic stopped integrals.',
                     'Actual closed integrands, a bounded stopping time and genuine stopping '
                     'measurability are explicit. This module does not alone identify the '
                     'continuous original noise at every random time.'),
 'StoppedIntegralRealization': ('Bounded stopping of actual continuous Brownian integrals',
                                'Continuous computed versions and dyadic stopped limits construct '
                                'actual continuous martingales whose paths satisfy the stopped '
                                'identity simultaneously at every observation time; exact '
                                'original-column weighted stopped energy follows.',
                                'Actual closed integrands and genuine bounded stopping events are '
                                'explicit. This intermediate API asks for Brownian coordinate '
                                'continuous paths, supplied by the proved valid continuous Driver '
                                'modification. Minimal-A1 localization and its coefficient '
                                'hypotheses remain distinct.'),
 'PartitionQuadraticEnergy': ('Finite-partition expected quadratic energy at weak drift regularity',
                              'An actual martingale, point-time L2 variables and an adapted '
                              'decomposition yield the exact finite-partition quadratic energy '
                              'identity, with stochastic left cross terms proved zero.',
                              'Point-time L2 and the literal adapted decomposition are explicit. '
                              'No time-L1(L2) drift, stochastic-isometry or energy conclusion is '
                              'assumed. Riemann/variation limits and localization remain '
                              'separate.')})


MODULES.update({'ConstructedContinuousIntegral': ('Continuous martingale versions with Brownian regularity '
                                   'derived',
                                   'The explicit continuous Driver modification and actual '
                                   'completed-integral invariance construct a continuous '
                                   'martingale version of every actual closed integral in the '
                                   'original filtration.',
                                   'Only the primitive actual Driver and literal closed integrand '
                                   'are supplied. No Brownian path continuity, filtration '
                                   'completion, stochastic-output identity or uniform convergence '
                                   'premise remains.'),
 'PartitionFiniteVariation': ('Pathwise drift-work and quadratic-variation limits',
                              'Original Bochner-L1 drift primitives and continuous state/noise '
                              'paths imply exact drift-work quadrature convergence and vanishing '
                              'finite-variation quadratic and cross terms.',
                              'The original raw path continuity and pathwise L1 drift are '
                              'explicit. No time-L1(L2) drift or variation-limit conclusion is '
                              'assumed. Probabilistic expectation/localization limits are '
                              'separate.')})


MODULES.update({'PartitionVariationBounds': ('Actual domination of finite-variation energy sums',
                              'Original drift total variation and actual state/noise radii bound '
                              'the finite-partition work, quadratic and cross sums, supplying '
                              'explicit localization domination estimates.',
                              'Actual raw pathwise Bochner-L1 drift and the displayed path radii '
                              'are explicit. No time-L1(L2) drift or dominated-convergence '
                              'conclusion is assumed; localized stochastic expectation limits '
                              'remain separate.')})


MODULES.update({'ProductLpSections': ('Constructed spatial L² sections of raw product fields',
                       'Literal raw spatial sections form actual Bochner time-L² curves; their norm, product '
                       'energy and pointwise realization are proved by an isometric currying construction.',
                       'Raw joint strong measurability and product square integrability are explicit. The '
                       'spatial measure is sigma finite and the Hilbert target separable. The field itself '
                       'determines a countably generated spatial subalgebra, enlarged by a finite-measure cover; '
                       'actual pullback derives the original section curve. No ambient measure separability, '
                       'coefficient curve or curve measurability is supplied.'),
 'CanonicalSeparable': ('Separable canonical initial and Brownian sample measures',
                        'Countability of the actual scalar-time Hilbert basis proves countable generation '
                        'and separability of canonical initial/noise and finite-particle sample measures.',
                        'The finite noise coordinate type and the displayed Borel second-countable initial '
                        'state space are explicit. No separability instance for the canonical Brownian '
                        'sample law is assumed.'),
 'RawDiffusionIntegral': ('Computed Brownian integration of original raw fields',
                          'Actual joint raw diffusion columns supply their own spatial L² sections and '
                          'predictable completion. Martingale representatives, continuous paths, zero input '
                          'and exact original-column weighted increment energy are derived.',
                          'Raw joint strong measurability, expected integrated square norm, actual AE '
                          'past-adaptation are explicit. Spatial sections now require no ambient measure separability. No L² curve, '
                          'approximation, stochastic isometry or continuous noise version is supplied.'),
 'RawDiffusionTransport': ('Original raw integrals under coupling and Driver changes',
                           'Product-AE coefficient agreement gives equality of actual computed raw '
                           'integrals. Measure-preserving pullback, valid filtration enlargement and '
                           'Brownian modification preserve those integrals.',
                           'Actual raw coefficient measurability, product square integrability, adaptation '
                           'and the proved measure-preserving or valid Driver identities are explicit. No '
                           'output-law or matching L² coefficient identity is assumed.'),
 'RawDiffusionAlgebra': ('Subtraction and synchronous energy of raw diffusion fields',
                         'Spatial sections commute with subtraction outside the actual time null set. The '
                         'computed raw integrals subtract exactly and have the original synchronous '
                         'difference weighted isometry.',
                         'Both raw fields are jointly strongly measurable, adapted and expected time-square '
                         'integrable. The metric weight is selfadjoint where required; no linearity or '
                         'stochastic energy conclusion is supplied.'),
 'PathEnergyStopping': ('Genuine first-hit stopping times from path energy',
                        'Continuous monotone adapted scalar path energies yield actual bounded first-hit '
                        'stops, their energy caps, threshold monotonicity and horizon exhaustion.',
                        'Continuity, monotonicity and current-past measurability of the actual path energy '
                        'are explicit. PathwiseLocalEnergy derives them for the literal local coefficient '
                        'integral. No stopping-time or cap conclusion is assumed.'),
 'PathwiseLocalEnergy': ('Literal local coefficient energy is continuous and adapted',
                         'The actual time integral of raw nonnegative local energy is continuous and '
                         'monotone, and progressive windows prove its current-past measurability. First-hit '
                         'properties follow for this literal energy.',
                         'Raw joint measurability, nonnegativity, pathwise time-L1 and actual progressive '
                         'window measurability are explicit. No preexisting continuous adapted energy or '
                         'stopping budget is supplied.'),
 'LocalizedDiffusion': ('Actual product-L² columns from first-hit localization',
                        'Literal raw columns masked by genuine first-hit stops have actual spatial/time L² '
                        'sections, past-adaptation and total expected energy bounded by the threshold.',
                        'The scalar local path energy controls the sum of original column squares and has '
                        'the displayed integral, continuity, adaptation and pathwise L1 properties. No '
                        'stopped coefficient curve or stochastic energy budget is supplied.'),
 'DriverNullAugmentation': ('Null augmentation preserves the actual Brownian Driver',
                            'Every augmented event has an original past event equal almost surely, '
                            'preserving joint future independence and all Driver fields on the same ambient '
                            'probability space. One AE continuous adapted process is regularized on one null '
                            'event.',
                            'Only ambient measurable null sets are added; the sample space and measure stay '
                            'literal. No Brownian independence in the augmented filtration is assumed.'),
 'PathwiseNullRegularization': ('One common null regularization of progressive local energy',
                                'An actual ambient measurable null event makes local path integrability hold '
                                'everywhere while preserving progressive windows and all original time '
                                'sections off that event.',
                                'Raw nonnegative progressive energy is only almost surely pathwise L1. The '
                                'null augmentation is explicit. A diffusion application must use the same '
                                'mask for both the scalar energy and physical columns.'),
 'RawIntegralStopping': ('Stopping the actual raw stochastic integral',
                         'Original raw coefficient masks have exactly the completed stopped domain. Genuine '
                         'bounded stopping and continuous computed versions then give one event of '
                         'simultaneous original-noise stopping identities.',
                         'Actual bounded stopping events, original product-L² adapted columns and computed '
                         'continuous versions are explicit. No random-time output equality, stopped-domain '
                         'identity or stopped SDE is supplied.'),
 'ConstructedStoppedIntegral': ('Bounded stopping without a Brownian continuity premise',
                                'The proved continuous Driver modification and original-integral invariance '
                                'remove the path-continuity premise from bounded stopped martingale '
                                'realization and original-column energy.',
                                'Only the primitive Driver, actual closed integrand and genuine bounded '
                                'stopping events are supplied. No noise version, martingale, random-time '
                                'realization or stochastic-isometry conclusion is assumed.'),
 'RawLocalIntegral': ('Constructed local Brownian integrals from raw local energy',
                      'First-hit restricted original columns give actual computed continuous martingales. '
                      'Their stopped consistency is proved; horizon exhaustion glues a local noise process '
                      'with simultaneous stopped identities.',
                      'Raw columns are jointly strongly measurable and AE adapted. A nonnegative progressive '
                      'pathwise-L1 scalar controls their square sum; no global expected coefficient moment, '
                      'local noise, stopped equation or energy conclusion is supplied.'),
 'RawLocalRegularization': ('Local diffusion data from almost-sure path integrability',
                            'One ambient null augmentation and a single common coefficient mask construct '
                            'actual everywhere-defined local diffusion data while preserving original '
                            'physical columns for every time on one probability-one event.',
                            'Original raw columns and scalar energy are jointly strongly measurable, '
                            'adapted/progressive and only AE pathwise locally integrable, with pointwise '
                            'square control. No global moment or stopped stochastic process is supplied.'),
 'RawStoppingCoordinates': ('Original raw equations derive their actual stopped equations',
                            'The literal state at min(time,stop) and masked raw drift satisfy exactly the '
                            'stopped original integral equation. Genuine eventual horizon exhaustion gives '
                            'pointwise original-state convergence.',
                            'Only the original simultaneous path equation and bounded nonnegative stop are '
                            'used. Joint measurability assumptions appear where needed; no stopped SDE, '
                            'stopped state moment or L² coordinate identity is supplied.'),
 'RawStoppingAdaptation': ('AE past-adaptation of actual stopped states',
                           'Finite dyadic stopping selections and a genuine measurable limit prove AE '
                           'current-past measurability of the original state evaluated at a bounded stopping '
                           'time.',
                           'The original state is AE adapted with almost-sure continuous paths, and genuine '
                           'stopping events are explicit. No complete filtration or all-path continuity is '
                           'assumed.'),
 'RawProgressiveWindow': ('Actual progressive windows in real time',
                          'Real-time restrictions and bounded windows of genuinely progressive processes '
                          'retain the actual past-product measurability used by local coefficient energies.',
                          'The process progressive measurability and displayed filtration/time restrictions '
                          'are explicit. No path-energy adaptation conclusion is supplied.'),
 'LinearGrowthMoment': ('Derived endpoint moments and coefficient integrability',
                        'Actual computed noise energy and original integral equations give a '
                        'Volterra-Gronwall moment bound. Fatou transfers localization bounds, and primitive '
                        'linear growth derives spatial and product-time coefficient L² membership.',
                        'Primitive nonnegative growth constants, initial L² and actual original equations '
                        'are explicit. Intermediate generic noise estimates remain visible only in their own '
                        'lemmas; the computed-noise endpoints derive them internally.'),
 'LinearGrowthHorizon': ('One moment constant for every time in the original horizon',
                         'The computed endpoint moment theorem applies at every subhorizon with the same '
                         'original integral horizon and a single localization-independent constant.',
                         'Actual original computed integral equations and primitive quadratic coefficient '
                         'growth are explicit. No change-of-noise-horizon identity or uniform moment '
                         'conclusion is supplied.'),
 'RawLinearGrowthState': ('Raw local strong equations derive global moments',
                          'Genuine first-hit stops, capped drift variation and actual computed noise give '
                          'localized spatial moments. The original linear growth gives a '
                          'localization-independent Volterra bound; Fatou derives original state moments and '
                          'global coefficient square integrability. The local noise is proved equal to the '
                          'original global computed integral.',
                          'The original simultaneous raw equation is driven by the constructed local '
                          'integral, initial state is L², raw drift is jointly measurable and controlled by '
                          'the local path energy, and the primitive linear-growth bound has nonnegative '
                          'constants. No original global moment, stopped equation, coefficient curve, '
                          'stochastic energy or local-to-global noise identity is supplied.'),
 'RawLinearGrowthModel': ('Original linear-growth Model data are constructed',
                          'Original coefficient identities transfer the derived raw state and coefficient '
                          'moments to the literal Model. The actual model integral equation, predictable '
                          'Model Data and exact original sampler laws follow.',
                          'The original local strong equation and primitive linear growth come from '
                          'RawLinearGrowthState. Actual optimizer ODE/integral data, observation domain, raw '
                          'coefficient measurability and coefficient realizations on one full-probability '
                          'event are explicit. No stronger Data, global moment, noise compatibility or '
                          'output-law premise is supplied.'),
 'RawToPredictableData': ('Raw original equations supply literal predictable Model data',
                          'Actual spatial sections and product Fubini construct every L² state/coefficient '
                          'curve and the original sampler integral equation, preserving the raw sampler law.',
                          'This intermediate factory explicitly requires raw fixed-time/product moments, raw '
                          'adaptedness, actual original computed equation, optimizer equation and '
                          'observation integrability. RawLinearGrowthModel derives its moment and '
                          'global-noise hypotheses from the original local linear-growth equation.'),
 'RawLocalStationarity': ('Source stationarity for the actual local strong equation',
                          'Frozen sampler invariance, zero mean gradient and the optimizer fixed point '
                          'construct the complete constant-optimizer original local equation. Same-driver '
                          'source uniqueness proves the literal stationary Dirac optimizer tensor sampler '
                          'law.',
                          'The original sampler has continuous adapted paths, pathwise Bochner-L1 drift and '
                          'an actual locally constructed diffusion integral; no time-L1(L2) drift or growth '
                          'is required. Source same-driver uniqueness, actual frozen invariant trajectory, '
                          'observation domain and matching initial variables remain explicit.'),
 'DoobStrongL2': ('Derived strong L² maximal martingale control',
                  'Conditional expectation, a finite running maximum and Young inequality prove the '
                  'factor-four strong maximal second-moment bound for actual martingales.',
                  'The actual L² martingale or nonnegative L² submartingale hypotheses are explicit. No '
                  'maximal-moment bound, tail-integrability or uniform-integrability conclusion is assumed.'),
 'MonotoneSquareRadius': ('Actual L² radii from increasing finite maxima',
                          'Monotone convergence of genuine increasing finite observation maxima constructs a '
                          'square-integrable countable radius with the same uniform second-moment bound.',
                          'The finite maxima and their actual uniform moments are explicit; no limiting '
                          'radius membership or maximal estimate is supplied.'),
 'StrongMartingaleRadius': ('Constructed square-integrable continuous martingale radii',
                            'Finite strong Doob, countable monotone maxima and dense-time continuous paths '
                            'construct an actual path radius with second moment at most four times terminal '
                            'energy.',
                            'An actual L² martingale and AE continuous paths on the finite horizon are '
                            'explicit. No path-radius variable or maximal second moment is supplied.'),
 'BoundedVariationRealization': ('L² drift primitives from bounded path variation',
                                 'Joint raw measurability and a literal pathwise total-variation cap '
                                 'construct actual spatial L² drift primitives and exact raw realizations.',
                                 'The drift is only pathwise Bochner L1 with bounded variation budget. No '
                                 'spatial L² drift value or time-L1(L2) drift is assumed.'),
 'BoundedVariationState': ('Actual stopped state moments from original equations',
                           'Initial L², actual noise L² and the original raw integral equation derive the '
                           'state L² value and its explicit three-term second-moment bound.',
                           'The original raw drift has a genuine pathwise variation cap and joint '
                           'measurability. No stopped state moment, stronger coefficient curve or '
                           'time-L1(L2) drift is supplied.'),
 'ExpectedBilinearLimits': ('Expectation limits of actual partition pairings',
                            'Literal weighted pairings of actual L² states and primitives have the required '
                            'measurability, integrability and expectation limits.',
                            'The displayed raw path convergence and genuine L² domination are explicit '
                            'intermediate hypotheses. Later raw finite-variation factories construct their '
                            'radii internally.'),
 'PathwiseMartingaleEnergy': ('Expected quadratic energy with pathwise L¹ drift',
                              'Actual martingale orthogonality and derived pathwise partition limits prove '
                              'the expected quadratic balance with the original drift primitive.',
                              'Original continuous state/noise paths, pathwise Bochner-L1 drift, point-time '
                              'L² and a square-integrable path radius are explicit. No time-L1(L2) drift or '
                              'energy balance is assumed.'),
 'PathwiseDriftFubini': ('Fubini for the actual localized drift work',
                         'Raw joint measurability, pathwise integrability and a genuine square-integrable '
                         'localization radius derive product work integrability and its actual '
                         'expectation/time interchange.',
                         'The raw paths and radius domination are explicit. No time-L1(L2) drift, product '
                         'work-integrability or Fubini conclusion is supplied.'),
 'RawFiniteVariationEnergy': ('Original raw quadratic balance with capped variation',
                              'The actual equation and actual continuous L² martingale construct all drift '
                              'primitives and maximal radii, then derive the original expected quadratic '
                              'energy.',
                              'Pathwise drift L1 with a literal total-variation cap, point-time state L² and '
                              'the actual martingale decomposition are explicit. No drift L² curve, '
                              'path-radius or final energy identity is supplied.'),
 'ConstructedRawFiniteVariationEnergy': ('Computed-noise quadratic balance under capped variation',
                                         'The original raw computed diffusion integral derives the '
                                         'martingale, spatial noise moments, path radius and exact '
                                         'original-column weighted quadratic balance.',
                                         'Actual raw drift pathwise L1 and variation cap, original '
                                         'state/noise equation, joint coefficient measurability and product '
                                         'square-integrable adapted diffusion are explicit. No martingale, '
                                         'isometry, radius or time-L1(L2) drift is supplied.'),
 'RawVariationWork': ('Actual original drift work on the sample-time product',
                      'The raw equation, genuine martingale and derived radius prove product integrability '
                      'of the original weighted drift work and the required Fubini identity.',
                      'The actual raw paths and bounded path variation are explicit; no drift L² curve or '
                      'work-integrability conclusion is assumed.'),
 'RandomVariationRealization': ('L² primitives under random square-integrable variation',
                                'A genuine random L² variation budget constructs spatial L² drift primitives '
                                'and exact raw integral realizations.',
                                'Only raw joint measurability, pathwise Bochner L1 and domination of actual '
                                'total variation by the given L² budget are supplied. No spatial L² drift or '
                                'final primitive membership is assumed.'),
 'RandomVariationEnergy': ('Raw expected energy with random variation budgets',
                           'The original raw equation and actual martingale construct the L² primitive and '
                           'maximal radius from a random square-integrable total-variation budget, yielding '
                           'the quadratic balance.',
                           'The original paths, actual martingale and random L² variation budget are '
                           'explicit. No time-L1(L2) drift, maximal radius or energy conclusion is '
                           'supplied.'),
 'RandomVariationWork': ('Fubini for random-budget original drift work',
                         'The original raw equation and actual martingale supply domination for original '
                         'work on the time-sample product, including random L² variation budgets.',
                         'Raw path continuity, joint drift measurability and the literal random variation '
                         'bound are explicit. No drift L² curve or final work-integrability premise is '
                         'supplied.'),
 'ConstructedRandomVariationEnergy': ('Computed quadratic balance with random path variation',
                                      'Actual raw Brownian integration derives all martingale, noise moment '
                                      'and maximal-radius inputs to the weak finite-variation energy balance '
                                      'under a random L² variation budget.',
                                      'Original raw equations, pathwise drift L1, actual random L² variation '
                                      'control and adapted product-square diffusion are explicit. No '
                                      'stochastic energy, radius or time-L1(L2) drift is assumed.'),
 'ConstructedRandomVariationHorizon': ('Weak quadratic balance at every original subhorizon',
                                       'The original computed Brownian horizon remains fixed while actual '
                                       'raw quadratic balance is proved at each earlier observation time.',
                                       'The original random-L² variation budget, raw equations, '
                                       'measurability and adapted square diffusion are explicit. No '
                                       'noise-horizon compatibility, martingale or energy conclusion is '
                                       'supplied.'),
 'ConstructedRandomVariationIntegral': ('Actual integral energy family with weak original drift',
                                        'The actual original drift work plus diffusion energy is integrable '
                                        'in time, and its primitive equals the expected quadratic energy '
                                        'difference at every subhorizon.',
                                        'Only original raw computed equations, continuous paths, pathwise L1 '
                                        'drift with random L² variation budget and adapted product-square '
                                        'diffusion enter. No time-L1(L2) drift, supplied generator/energy '
                                        'family or stochastic isometry is assumed.'),
 'DampedContinuation': ('Actual exponential continuation after stopping',
                        'The literal stopped original state is continued by deterministic rate-rho '
                        'exponential damping. Its exact raw drift, primitive and dissipation identities are '
                        'proved.',
                        'The original pathwise equation and genuine bounded stop are explicit. No stochastic '
                        'product rule or after-stop energy inequality is supplied.'),
 'RawParticleDissipation': ('Original particle dissipation and damping from source A3',
                            'The actual empirical coupling and source joint monotonicity derive the original '
                            'full particle/copy generator bound. Literal damping retains the sharp rate '
                            'after stopping while the forcing remains the original reference observation '
                            'fluctuation.',
                            'Positive particle count, source A3, the original coefficient identities, '
                            'deterministic reference optimizer and response Lipschitz constant are explicit. '
                            'No iid law for the artificial damped cloud or final dissipation conclusion is '
                            'assumed.'),
 'ConstantNoiseWork': ('Explicit one-sided work criterion for constant diffusion',
                       'Source A3 yields frozen pointwise sampler dissipation through actual one-point laws. '
                       'The remaining positive work is confined to parameter-cross drift; explicit '
                       'sufficient integrability criteria are proved.',
                       'The parameter-cross work integrability or displayed '
                       'parameter-Lipschitz/linear-growth sufficient condition is an additional explicit '
                       'hypothesis. This does not assert that the minimal constant-diffusion branch A1(i) '
                       'alone supplies it.')})


MODULES.update({'RawLinearGrowthLaw': ('True initial-Wasserstein contraction of original raw linear-growth solutions',
                        'Primitive local raw Model equations and linear growth derive global moments and '
                        'computed predictable realization. The true initial optimal-coupling distance '
                        'contracts for the literal original raw output laws.',
                        'Original canonical initial coordinates, P2 initial laws, raw local strong '
                        'realizations, source A3 and measurable original coefficients are explicit. No '
                        'global moment, coefficient curve, noise equality, output-law or all-couplings '
                        'realization premise is supplied.'),
 'OptimizerHorizonBounds': ('A finite parameter bound from the original optimizer equation',
                            'The optimizer integral equation with merely L1 drift yields actual path '
                            'continuity. Compactness gives a nonnegative finite bound for every continuous '
                            'parameter projection along the original trajectory.',
                            'Only the original finite-horizon optimizer integral equation, its genuine '
                            'integrable drift and continuity of the parameter projection are supplied. No '
                            'optimizer pointwise derivative, trajectory-continuity or parameter-bound '
                            'conclusion is assumed.'),
 'RawLocalNoiseGlobalization': ('Local noise equals global integration from actual diffusion moments',
                                'Actual stopped integral identities and horizon exhaustion prove local noise '
                                'equals the original global computed raw integral whenever original '
                                'diffusion expected energy is finite.',
                                'Only original diffusion product-square integrability is additional. No '
                                'drift growth, state moment, drift L2 curve or local-to-global stochastic '
                                'identity is supplied.'),
 'ConstructedRandomVariationWork': ('Computed original work is product integrable with random variation',
                                    'Actual computed noise, original raw equations and a random '
                                    'square-integrable total-variation budget derive product integrability '
                                    'of the literal weighted drift work.',
                                    'Raw joint measurability, continuous original paths, actual coefficient '
                                    'square integrability and the random L2 variation budget are explicit. '
                                    'No original drift L2 curve, supplied martingale, maximal radius or '
                                    'work-integrability premise enters.'),
 'PositiveWorkFubini': ('One-sided work yields exact raw expected energy',
                        'Pathwise Bochner-L1 dynamics imply the literal quadratic fundamental theorem. '
                        'Integrability of only positive work yields full product absolute-work '
                        'integrability, expected balance and decay, without a total-variation L2 budget.',
                        'Nonnegative quadratic energy, initial-energy integrability, actual path equation '
                        'and positive-work integrability are explicit. The last condition is an additional '
                        'analytic criterion. NaturalFiniteWorkContraction derives it from the explicit finite signed-work convention; A4/A5 derive it for stationary-target comparisons.')})


MODULES.update({'RawLocalNoiseCongruence': ('Actual common-diffusion local noise agrees simultaneously',
                             'Original globally square-integrable raw diffusion columns with product-AE '
                             'equality give identical local noise at every deterministic time. Actual '
                             'continuous paths and a dense sequence upgrade this to one event on the whole '
                             'horizon.',
                             'Both original raw diffusion product-square moments and their product-AE '
                             'identity are explicit; no drift growth or state moment is imposed. No noise '
                             'cancellation, gauge independence or simultaneous output identity is supplied.')})


MODULES.update({'BrownianPathSpace': ('Actual continuous Brownian paths have universal Wiener law',
                       'A single measurable null cover constructs actual continuous scalar/vector path '
                       'variables. Their Borel algebra is generated by raw evaluations; projective '
                       'finite-dimensional uniqueness proves the Wiener law and independent product law.',
                       'Only original Brownian laws, actual evaluation measurability and path continuity '
                       'enter the generic scalar/vector statements. The generic vector theorem exposes '
                       'coordinate independence; BrownianDriverPathLaw derives it from every primitive '
                       'Driver. No inverse onto unused Gaussian seed directions or final product-law match '
                       'is assumed.'),
 'ProcessPathIndependence': ('Whole coordinate independence from finite Driver grids',
                             'Finite-dimensional projective uniqueness promotes actual finite-grid '
                             'independence to independence of original complete raw coordinate paths. Every '
                             'primitive Driver therefore has whole coordinate-path independence.',
                             'Only finite-grid independence and original evaluation measurability are '
                             'required by the generic theorem; DriverPathIndependence derives the '
                             'finite-grid input from the Driver. No whole-path independence is supplied.'),
 'InitialPathIndependence': ('Whole-noise independence from finite initial observations',
                             'Actual projective measure uniqueness proves the full original initial/path '
                             'product law from independence of every finite noise observation.',
                             'The time type is nonempty, original evaluations and initialization are '
                             'measurable, and finite-dimensional initialization/noise independence is '
                             'explicit. DriverInitialIndependence derives it for actual time-zero past '
                             'variables.'),
 'BrownianDriverPathLaw': ('Every Driver gives a genuine initial/Wiener-path probability map',
                           'Finite-grid results derive whole-coordinate and initial/noise independence. The '
                           'actual continuous Brownian modification gives a measurable initial/path map '
                           'preserving exactly original-initial-law times product Wiener law.',
                           'The actual initial variable is ambient measurable and AE measurable in the '
                           'original time-zero past. No Brownian path continuity, whole-path independence, '
                           'product-law identity or Gaussian-seed inverse is supplied. Path evaluations '
                           'equal the original Driver at each fixed time almost surely; simultaneous '
                           'equality to arbitrary raw pre-Brownian paths is not asserted.'),
 'DriverPathIndependence': ('Spatial and temporal independence from primitive Drivers',
                            'Future-vector independence and same-interval spatial independence give '
                            'independent time-grid increments, finite coordinate histories and finite '
                            'Brownian value rows.',
                            'Only the primitive actual Driver is used. ProcessPathIndependence then extends '
                            'these actual finite-grid laws to complete raw coordinate paths; no whole-path '
                            'independence premise is added.'),
 'DriverInitialIndependence': ('Time-zero information is independent of finite Brownian histories',
                               'The actual initial variable and all finite joint-vector Brownian evaluations '
                               'have a derived independent law, including an AE time-zero measurability '
                               'version.',
                               'The initial variable is strongly or AE strongly measurable in the original '
                               'time-zero filtration. No initial/noise independence or finite-array '
                               'product-law conclusion is supplied.'),
 'DriverPushforward': ('Valid Brownian Drivers descend through probability maps',
                       'Actual finite-dimensional laws, spatial increment independence and future-past '
                       'independence transport along a measure-preserving map, constructing all target '
                       'Driver fields.',
                       'Actual probability preservation, target evaluation adaptation, fixed-time AE '
                       'source/target process identities and target-past comap inclusion are explicit. These '
                       'are structural input-map conditions, not a supplied target Brownian law or '
                       'independence claim.'),
 'NaturalPastTransport': ('Natural path filtrations fit the proved null-augmented past',
                          'An ambient-measurable version of an AE past-measurable variable is actually '
                          'measurable in the same past augmented by ambient null sets. Entire natural path '
                          'filtrations therefore pull into that valid augmented Brownian filtration.',
                          'Actual ambient measurability and AE past adaptation are explicit. No complete '
                          'filtration, causal equality on exceptional paths or future-independent null '
                          'augmentation is assumed; the latter was proved separately.'),
 'BrownianPathDriver': ('Canonical initial/Wiener-path Driver with full joint past',
                        'The proved initial/path probability map pushes an original canonical Brownian '
                        'source to literal independent initial state and Wiener paths. Its evaluation '
                        'process and full joint initial/path natural filtration form an actual Driver.',
                        'The initial law is a probability on the displayed Borel second-countable state '
                        'space. Brownian laws, spatial and whole-path independence, initial independence and '
                        'the input product law are derived; no unrelated Gaussian-seed inverse is required.'),
 'RawLocalPullback': ('Original raw local diffusion fields under probability transport',
                      'Actual locally integrable physical columns and scalar energy pull along genuine '
                      'probability maps into valid enlarged filtrations. The intermediate global-square '
                      'noise theorem identifies their computed local output.',
                      'Only primitive raw local fields, measure preservation and valid past/noise '
                      'compatibility are structural inputs. The stronger noise theorem explicitly assumes '
                      'global diffusion expected energy; RawLocalPullbackLocal removes that intermediate '
                      'restriction.'),
 'RawLocalPullbackLocal': ('Local-noise transport without global coefficient moments',
                           'First-hit stops pull back literally; actual stopped integrals obey proved '
                           'probability transport and their continuous exhausted limits give one event of '
                           'complete-horizon local noise equality.',
                           'Only samplewise local square integrability of the original columns and actual '
                           'measure-preserving, valid Driver transport enter. No global expected diffusion '
                           'moment or supplied local-noise matching conclusion is required.'),
 'RawLocalSolutionTransport': ('Original raw strong equations preserve their actual laws',
                               'Original sampler and optimizer local equations transport to valid common '
                               'Brownian spaces with all output marginals derived. Same-driver uniqueness '
                               'then gives actual cross-space solution-law equality and stationary-law '
                               'transfer.',
                               'The actual measure-preserving initial/noise map and valid past/evaluation '
                               'compatibility are explicit. No global coefficient moment, noise matching '
                               'conclusion, output-law equality or time-L1(L2) drift is supplied.'),
 'RawLocalGauge': ('Actual local Brownian noise is independent of energy gauge',
                   'Double-stopped computed integrals agree for original raw diffusion fields equal on one '
                   'all-time full-probability event. Actual gauge exhaustion derives simultaneous horizon '
                   'equality of their local noise.',
                   'Only actual locally square-integrable raw columns with one-event horizon equality are '
                   'used; gauges may differ. No global expected diffusion square, drift growth or '
                   'gauge/noise identity is supplied.'),
 'RawFrozenKernel': ('Invariant frozen kernels construct actual stationary sampler data',
                     'The actual jointly measurable frozen solver defines a transition kernel by '
                     'Brownian-seed integration. Product Fubini identifies kernel action with original '
                     'solver marginals, so kernel invariance derives all-time stationary sampler output '
                     'laws.',
                     'An actual frozen raw solver with the original initial coordinate is explicit. No '
                     'marginal-law stationarity conclusion is supplied. Existence of a frozen strong solver '
                     'or a weak-to-strong realization is not proved by this intermediate kernel '
                     'construction.'),
 'RawConstantNoiseContraction': ('Original constant-noise contraction from one-sided work',
                                 'Actual common constant diffusion cancels in the original local equations. '
                                 'Pathwise L1 drift and positive-work Fubini then let literal source A3 '
                                 'derive expected quadratic and RMS decay.',
                                 'The original raw strong equations and explicit parameter-cross '
                                 'positive-work integrability are required. No drift time-L1(L2), L2 '
                                 'total-variation budget, noise cancellation or energy conclusion is '
                                 'assumed. Minimal A1(i) alone is not asserted to imply the extra work '
                                 'condition.'),
 'RawConstantNoisePullback': ('Law-preserving raw constant-noise coupling realizations',
                              'Original raw constant-diffusion model equations and actual marginal laws pull '
                              'to valid common Brownian spaces, using computed local-noise naturality.',
                              'Actual measure-preserving input maps and Driver past compatibility are '
                              'explicit. No global drift moment, supplied noise/output identity or '
                              'coupling-energy conclusion enters.'),
 'RawConstantNoiseLaw': ('True optimal-law constant-noise contraction under explicit work',
                         'Every initial coupling receives an actual law-preserving common Brownian '
                         'realization of the original raw equations. One-sided work gives contraction, then '
                         'genuine coupling infima give the true initial-Wasserstein factor.',
                         'Parameter-cross L1 work is explicit on the constructed joint realizations. This is '
                         'an additional sufficient criterion for A1(i), not a proof that the bare source '
                         'constant-diffusion alternative supplies it. No final output-law or transport '
                         'inequality is assumed.'),
 'RawDampedState': ('Sharp raw localization by literal after-stop damping',
                    'Actual original local strong equations yield genuine stopped equations, continuous '
                    'martingale radii, after-stop damped paths and integrable random variation budgets. The '
                    'original computed weak energy family follows without global drift moments.',
                    'Initial L2, original continuous adapted paths, joint raw drift measurability, genuine '
                    'local path energy and original simultaneous equation are explicit. No stopped SDE, '
                    'radius, drift L2 curve, work estimate or energy conclusion is supplied.'),
 'RawParticleForcing': ('The original iid reference gives sharp damped-state forcing',
                        'Actual original reference-cloud variance controls residual work against any '
                        'square-integrable damped vector, deriving the exact variance/N forcing.',
                        'Only the original reference cloud has its iid population marginal. No independence '
                        'of interacting particles or iid law for artificially damped reference coordinates '
                        'is assumed. Response Lipschitz and original observation square '
                        'integrability/variance are explicit.'),
 'RawParticleInteraction': ('Exact original particle interaction under local Brownian equations',
                            'Damped original localizations derive sharp forced energy before Fatou removes '
                            'the threshold. The actual original empirical Wasserstein RMS has exactly the '
                            'source interaction floor.',
                            'Original raw physical drift/diffusion identities, continuous adapted state, '
                            'initial L2 and simultaneous local-integral equation are explicit. Positive '
                            'N/rho, source A3, response Lipschitz, original reference iid '
                            'marginal/deterministic optimizer, uniform observation variance and synchronous '
                            'initialization remain visible. No linear growth, global drift moment, weak '
                            'test, work estimate, stochastic isometry or energy conclusion is supplied.'),
 'RawParticleParameter': ('Original raw parameter error and joint large-time/particle limit',
                          'The exact raw particle interaction and actual one-Lipschitz parameter projection '
                          'derive original parameter L2 and RMS. Reference relaxation yields source4 '
                          'constants, and a uniform family has joint time/particle limit zero.',
                          'Raw particle hypotheses are inherited. This version explicitly supplies an actual '
                          'reference weak solution, frozen weak stationarity, quadratic test domain and '
                          'synchronous realization for every initial coupling; these are not inferred from '
                          'an empty test family. No weak-particle equation, particle energy or parameter '
                          'triangle conclusion is assumed.'),
 'ConstantNoiseFluctuation': ('Source fluctuations control the actual constant-noise positive work',
                              'Dirac source A3 and response Lipschitz bound positive raw coupling work by '
                              'original gradient fluctuations. Uniform reference variance and target '
                              'observation L1 derive the required work Fubini and mean-field contraction for '
                              'this target comparison.',
                              'Actual raw constant-diffusion equations, source A4/A5 and a stationary target '
                              'are explicit. No cross-drift growth, work, energy or noise cancellation is '
                              'supplied. These fluctuation assumptions strengthen the unrestricted source2 '
                              'hypothesis; they are appropriate to the source4 target comparison.'),
 'RawConstantParameter': ('Raw constant-noise target error from source response and variance',
                          'Actual raw same-driver reference and stationary-target equations use source '
                          'response Lipschitz and uniform fluctuations to derive relaxation; the raw '
                          'particle triangle gives actual target parameter error.',
                          'The original raw mean-field and particle data, actual stationary-target law, '
                          'source A3/A4/A5 and original initial coupling are explicit. This result uses the '
                          'realized initial-coupling RMS; optimal initial-law infimum requires its separate '
                          'law construction. No abstract weak realizer or final work/energy premise is '
                          'supplied.')})


MODULES.update({'ContinuousProcessRepresentative': ('One simultaneous jointly measurable continuous process version',
                                     'Fixed-time measurability and almost-sure path continuity yield a '
                                     'jointly strongly measurable process with every path continuous and one '
                                     'full-measure event preserving every original time value.',
                                     'The time index is metrizable and second countable, and the state is a '
                                     'second-countable Borel normed space. No joint process version, '
                                     'adaptedness conclusion, stochastic law or moment is supplied.'),
 'CountableProductDependence': ('Countable spatial dependence inside arbitrary sample spaces',
                                'Every product-measurable field valued in a countably generated state space '
                                'remains measurable over an actual countably generated spatial subalgebra of '
                                'its original sample algebra.',
                                'This is exact measurable dependence, not an assumed ambient measure '
                                'separability or an almost-everywhere factorization. ProductLpSections adds '
                                'a genuine finite-measure cover before constructing its spatial L2 curves.'),
 'RawIntegralCLM': ('Computed raw Brownian integration commutes with state maps',
                    'Actual finite predictable coefficients and Brownian sums, literal closed predictable '
                    'domains, time cuts and raw spatial sections commute with every given bounded linear '
                    'state map.',
                    'The original raw field is jointly strongly measurable, adapted and square integrable on '
                    'the finite horizon. Transformed measurability, square integrability and adaptation are '
                    'derived. No matching coefficient curve, stochastic output or integral identity is '
                    'assumed.'),
 'RawPathSolutionTransfer': ('Source uniqueness transfers actual solution laws through Wiener paths',
                             'The proved initial/Wiener-path probability map pulls the canonical full '
                             'mean-field strong solution to each original source. Source same-driver '
                             'uniqueness then identifies original laws; a stationary weak frozen sampler on '
                             'another source yields the literal stationary product law.',
                             'A1 supplies one actual canonical full-system solution and same-driver '
                             'uniqueness. A2 is interpreted as an actual stationary weak frozen SDE '
                             'realization on some probability space. No common-source frozen strong solver, '
                             'assumed input/output law, global drift moment or noise matching is supplied.'),
 'RawConstantNoisePositiveLaw': ('Optimal-law contraction from one-sided integrable constant-noise work',
                                 'Original raw constant-diffusion equations have actual law-preserving '
                                 'initial-coupling realizations. Positive-work Fubini and the true '
                                 'Wasserstein infimum derive the optimal initial-law contraction factor.',
                                 'Positive joint work must be integrable on the constructed couplings. This '
                                 'explicit extra criterion is not derived from the bare source A1(i). No '
                                 'energy, noise cancellation or output-law conclusion is assumed.'),
 'RawLocalDriftEnergy': ('Natural drift-energy gauges for the original local equation',
                         'A common measurable null-set normalization adds the actual pathwise drift norm to '
                         'the diffusion gauge and preserves the original local Brownian noise on one '
                         'full-measure event.',
                         'Original raw drift joint measurability, past progressivity and almost-sure '
                         'pathwise L1 are explicit. Drift domination, the new gauge, coefficient identities '
                         'and all-time local-noise equality are derived; no global drift moment is '
                         'required.'),
 'RawIndependentCopies': ('Actual independent raw reference solutions on the product Brownian source',
                          'The finite product sample law carries a proved full-past Brownian Driver. '
                          'Evaluation pullbacks preserve each original raw SDE, and the actual reference '
                          'cloud has its iid marginal law and independent complete trajectories.',
                          'The original raw one-copy solution and a countably generated source are explicit '
                          'in this construction. Neither independence of interacting variables, a final iid '
                          'output law, nor a coordinate SDE matching premise is supplied. Full physical '
                          'cloud packing is separate.'),
 'RawSamplerGrowth': ('Primitive linear growth constructs the original model realization',
                      'Natural original raw strong equations and primitive joint linear growth derive the '
                      'parameter radius, drift gauge, global coefficient moments, local-to-global noise '
                      'identity and actual predictable model data.',
                      'Joint raw coefficient measurability, progressivity, Borel coefficient maps and the '
                      'original continuous adapted local equation are explicit. No global moment, '
                      'drift-control gauge, matching noise or stronger process package is supplied.'),
 'RawSamplerGrowthLaw': ('The linear-growth branch with the true initial law infimum',
                         'Canonical original raw solutions under primitive growth have actual law-preserving '
                         'realizations on every initial coupling. Source A3 yields the exact '
                         'condition-number contraction factor times the genuine initial Wasserstein '
                         'distance.',
                         'Canonical original equations, primitive growth/regularity, initial coordinate '
                         'identities and source A3 are explicit. Global moments, coupling outputs, noise '
                         'matching and final work/energy estimates are derived.'),
 'RawSolutionLawUniqueness': ('Actual law uniqueness across distinct Brownian sources',
                              'A proved initial/Wiener-path map and source pathwise uniqueness identify the '
                              'optimizer and raw sampler laws of solutions on distinct original probability '
                              'spaces.',
                              'One canonical full-system strong-solution witness with the same initial law '
                              'and source same-driver uniqueness are explicit A1 instances. No final '
                              'output-law equality, common-source frozen solution or global coefficient '
                              'moments are assumed.'),
 'RawSamplerGrowthArbitraryLaw': ('Linear-growth law contraction across original probability spaces',
                                  'Actual cross-source law uniqueness transfers the canonical '
                                  'optimal-coupling contraction to the original raw solutions, retaining the '
                                  'exact initial-law Wasserstein factor.',
                                  'The canonical solutions satisfy primitive original raw growth and '
                                  'regularity, with source same-driver uniqueness on the proved valid '
                                  'drivers. No original output matching, noise identity, moment bound or '
                                  'coupling inequality is supplied. The bare constant-diffusion alternative '
                                  'remains separate.')})

MODULES.update({'RawIntegralNoiseEmbedding': ('Actual Brownian coordinate inclusion and zero columns',
                               'Injecting finite Brownian coordinates into a larger valid Driver and padding '
                               'the original diffusion by zero preserves the actual finite sums, completed '
                               'domains and computed raw integral.',
                               'The index injection and actual coordinate identities are explicit. '
                               'Coefficient embeddings, zero-column sums, approximation and integral '
                               'equality are derived; no stochastic-output equality is supplied.'),
 'RawLocalLinearMap': ('Bounded linear maps of original local Brownian noise',
                       'The actual mapped diffusion and scaled common local gauge yield stopped-noise '
                       'identities. Genuine localization and gauge invariance prove one probability-one '
                       'event of original local-noise commutation.',
                       'Only the original local diffusion data and the given bounded linear map are '
                       'required. No global expected coefficient moment, final noise matching or energy '
                       'identity is supplied.'),
 'RawNaturalConstantNoise': ('Natural original constant-diffusion equations enter one-sided work analysis',
                             'A joint continuous sampler representative, the literal constant diffusion '
                             'gauge and actual local-noise invariance construct the raw constant-noise '
                             'comparison data from the original model solution.',
                             'Original local strong equations, constant model diffusion and primitive Borel '
                             'coefficient composites are explicit. No drift growth, positive-work '
                             'conclusion, extra moments or matching process package is supplied.'),
 'RawNaturalConstantParameter': ('Source target comparison from natural original constant-noise solutions',
                                 'Natural original raw mean-field solutions and a stationary target derive '
                                 'the positive-work criterion through response Lipschitz and reference '
                                 'variance. The actual law and parameter relaxation bounds follow.',
                                 'Primitive Borel maps, source A3/A4/A5, actual stationary target and its '
                                 'observation L1 are explicit. This version uses the genuine realized '
                                 'initial coupling cost; an optimal-law infimum needs its separate '
                                 'all-couplings construction. No stronger process, energy, cross-drift '
                                 'growth or final work premise is supplied.'),
 'RawReferenceCloud': ('Physical Hilbert state and diffusion for original independent copies',
                       'The flattened Hilbert reference cloud has actual physical diffusion columns, a local '
                       'energy formed from the genuine coordinate gauges, its complete P2 law, continuous '
                       'paths and joint measurable representative.',
                       'The one-copy original raw solution and finite independent complete seeds are '
                       'explicit. Physical coefficient identities and iid laws are derived. This module does '
                       'not infer a cloud equation from matching coordinate laws; RawReferenceCloudEquation separately proves the complete physical equation using actual local-noise transport. '
                       'alone.')})

MODULES.update({'RawLocalNoiseEmbedding': ('Actual local noise is unchanged by zero-padded coordinate inclusion',
                            'The original local diffusion columns embed through a genuine finite noise-index '
                            'injection. Exact stopped computed integrals and actual gauge exhaustion derive '
                            'one event of all local-noise identities.',
                            'Only original local diffusion, the index injection and actual Driver coordinate '
                            'identities are explicit. No global coefficient moment, noise-output matching or '
                            'final stochastic equation is supplied.'),
 'RawNaturalConstantLaw': ('Natural constant-noise target relaxation with the true law distance',
                           'Source response Lipschitz and reference variance derive positive work for the '
                           'natural original reference/target equations. Actual coupling transports and the '
                           'genuine infimum give the initial optimizer/Wasserstein factor.',
                           'Canonical original raw reference and stationary-target equations, primitive '
                           'Borel fields, source A3/A4/A5 and target observation L1 are explicit. No extra '
                           'growth/work/moment, old-process package or output-noise identity is supplied.'),
 'RawNaturalConstantLawParameter': ('The exact source parameter prefactor from natural target equations',
                                    'Natural original constant-noise reference/target solutions have the '
                                    'genuine optimal-law relaxation factor. Combining this with the original '
                                    'raw particle floor gives the exact source4 parameter expression.',
                                    'The actual physical particle/copy raw Data remain explicit until the '
                                    'final natural pairing factory. Source A3/A4/A5, primitive Borel maps, '
                                    'actual target stationarity and observation L1 are visible. No final '
                                    'work, moment, weak realizer, coupling output or parameter triangle is '
                                    'assumed.'),
 'RawReferenceCloudEquation': ('The physical independent reference cloud solves its actual SDE',
                               'Bounded linear state-map and noise-index-injection identities derive the '
                               'coordinate noises and the complete original Hilbert-cloud stochastic '
                               'equation from the physical diffusion columns. Its reference marginal law is '
                               'also derived.',
                               'The original one-copy raw solution and finite independent complete seeds are '
                               'explicit. Neither ambient countable generation/separability nor '
                               'coefficient/noise/law/equation matching is supplied. Packing this cloud with '
                               'a separate interacting original solution is the next assembly layer.')})

MODULES.update({'UniversalMomentGrowth': ('Universal finite-moment integrability forces pointwise growth',
                           'A genuine countable atomic probability construction proves that integrability of '
                           'a field against every law with finite given weight implies a uniform pointwise '
                           'weighted norm bound.',
                           'The weight is at least one and the universal integrability quantifier is '
                           'explicit. No growth bound, source energy inequality or solution regularity is '
                           'supplied.'),
 'MonotoneLocalBound': ('Actual finite-dimensional monotonicity gives compact bounds',
                        'Finite test vertices bound every component of an everywhere-defined monotone field. '
                        'A finite open cover derives uniform auxiliary-variable growth on compact parameter '
                        'sets.',
                        'Finite dimensionality, an actual orthonormal basis and the displayed pointwise '
                        'monotonicity/growth data are explicit. No continuity, local boundedness or '
                        'compact-uniform conclusion is assumed.'),
 'DiracOptimizerGrowth': ('The explicit finite-work convention controls Dirac optimizer growth',
                          'Source A3 on one-point empirical laws and universal finite signed coupling work '
                          'derive quadratic weighted Dirac-optimizer growth and compact-uniform positive '
                          'sampler-work bounds.',
                          'FiniteCouplingWork independently requires actual signed sampler work integrable '
                          'for every joint probability law with finite quadratic weight. It is not inferred '
                          'from conditional TwistedJointMonotonicity, and no optimizer Lipschitz or '
                          'positive-work conclusion is assumed.'),
 'DiracSamplerCoercivity': ('Dirac A3 gives primitive compact drift anchors and radial coercivity',
                            'The actual weighted full Dirac field is monotone. Finite-dimensional local '
                            'boundedness yields compact optimizer drift-anchor bounds, and frozen '
                            'dissipation derives a uniform radial Lyapunov work bound.',
                            'Actual source A3, nonnegative rate and the displayed metric/projections are '
                            'explicit. Universal finite work, drift norm growth, global state moments and a '
                            'Lyapunov conclusion are not supplied.'),
 'FiniteWorkPositiveIntegrability': ('Finite signed work derives the positive-work Fubini condition',
                                     'Universal finite signed coupling work gives compact-uniform quadratic '
                                     'positive sampler work. Actual product-L2 states and the original '
                                     'optimizer integral equations yield integrable positive joint work.',
                                     'FiniteCouplingWork is explicit and distinct from conditional A3. '
                                     'Product-L2 state moments are inputs to this intermediate lemma and '
                                     'derived independently by coercive stopping in the natural pipeline. No '
                                     'response Lipschitz, drift moment, energy identity or final contraction '
                                     'is assumed.'),
 'FiniteWorkScopeAudit': ('A checked distinction between finite and extended-negative signed work',
                          'An actual probability law has finite quadratic moment but nonintegrable fourth '
                          'power. The scalar drift -x-x^3 is pointwise strongly dissipative, yet its signed '
                          'coupling work against zero is not integrable for that P2 law.',
                          'No stochastic contraction counterexample is claimed. The result demonstrates that '
                          'universal finite signed work is substantive; an extended-negative-work '
                          'interpretation includes more superlinear systems.'),
 'RawCoerciveMoment': ('Original raw coercivity derives global second moments',
                       'Genuine stopped equations, exact local energy and Fatou derive a uniform original '
                       'second-moment budget and product-time L2 state integrability from one-sided radial '
                       'work control and bounded diffusion energy.',
                       'The actual raw original local equation, positive metric coercivity, initial L2 and '
                       'pointwise Lyapunov/diffusion constants are explicit. No global drift moment, state '
                       'moment, expected energy identity or final Fubini condition is supplied.'),
 'RawDampedPullback': ('Original controlled local equations transport without global moments',
                       'Actual local-integral naturality pulls state, drift, localization control and '
                       'initial moment through a genuine probability map, preserving the original raw '
                       'equation.',
                       'Measure preservation and valid common Driver identities are structural inputs. No '
                       'global expected diffusion square, output-law match or pulled stochastic equation is '
                       'assumed.'),
 'RawDriftGauge': ('Original pathwise drift gains a genuine local variation gauge',
                   'A common null augmentation normalizes the original almost-surely locally integrable '
                   'drift and adds its actual norm to the local energy, deriving controlled original raw '
                   'data.',
                   'Joint drift measurability, a.s. pathwise L1, progressive norm and the original local '
                   'equation are explicit. No expected variation budget, global drift moment, noise match or '
                   'energy conclusion enters.'),
 'RawDeterministicODE': ('The original optimizer equation has literal zero Brownian columns',
                         'An actual deterministic optimizer integral equation is encoded as local raw '
                         'dynamics. Bounded-linear-map naturality proves its constructed Brownian noise '
                         'vanishes.',
                         'Ordinary pathwise/integral ODE data and the actual Driver are explicit. No '
                         'zero-noise output identity or stronger stochastic-process package is supplied.'),
 'RawOptimizerField': ('Primitive Borel maps derive the original population field measurability',
                       'A jointly continuous sampler representative and actual population observation '
                       'integrals construct a measurable horizon extension of the optimizer field, '
                       'preserving its exact original values and integrability.',
                       'Original raw model data and primitive Borel observation/response composites are '
                       'explicit. No coefficient growth, diffusion constancy, global drift moment or '
                       'supplied population-field measurability is assumed.'),
 'RawNaturalSampler': ('Natural original sampler equations yield controlled raw dynamics',
                       'A joint continuous representative, proved null augmentation and primitive Borel '
                       'drift derive progressivity, a genuine variation gauge and an actual raw realization '
                       'with all original state/coefficient/noise identities on one event.',
                       'Natural original local sampler equations and primitive coefficient measurability are '
                       'explicit. No growth, global drift L2, expected variation, stronger raw Data or '
                       'energy conclusion is supplied.'),
 'RawPairDynamics': ('Actual original local equations pair on the common Brownian source',
                     'The paired physical diffusion and genuine local gauge are constructed. Actual state '
                     'projections of the computed local integral derive both original noise equations and '
                     'their paired raw realization.',
                     'Two actual original controlled local equations on the same finite Brownian Driver are '
                     'inputs. No global coefficient moments, matching paired noise/output law or final '
                     'energy is assumed.'),
 'RawNaturalConstantArbitraryLaw': ('Natural target law relaxation on arbitrary original sources',
                                    'Actual Wiener-path strong-solution transfer identifies original '
                                    'solutions with canonical comparison processes, then source A4/A5 derive '
                                    'target positive work and the true initial Wasserstein factor.',
                                    'A1 canonical actual existence and same-driver uniqueness, primitive '
                                    'Borel fields, actual stationary target and source A3/A4/A5 are visible. '
                                    'No growth, work, global moments, output-law equality or stronger '
                                    'process interface is supplied.'),
 'RawNaturalConstantArbitraryParameter': ('The exact source4 parameter factor on arbitrary original sources',
                                          'Actual cross-source law transfer, natural target relaxation with '
                                          'genuine initial Wasserstein distance and the raw particle floor '
                                          'derive the original random parameter bound.',
                                          'Natural original reference/target equations, A1 '
                                          'witness/uniqueness, A2 stationarity, A3/A4/A5 and actual physical '
                                          'particle/copy raw Data remain visible. No final law/energy/work '
                                          'or weak-coupling conclusion is assumed; the natural physical '
                                          'particle pairing is its separate input layer.')})

MODULES.update({
 'ProjectedFiniteWork': ('The projected criterion exposes the universal finite U5 domain',
   'Constant diffusion cancels the difference columns, so the named ordinary finite signed-integral domain of U5 gives FiniteCouplingWork. The full canonical spectral criterion then returns positive rate, actual joint monotonicity and that domain together.',
   'The universal finite sampler-drift domain is explicit and independent of the conditional U4/U5 inequalities. Primitive matrices, coordinate projections and all original criterion hypotheses remain; no stochastic energy or law-contraction conclusion is assumed.'),
 'RawConstructedParticleCopy': ('Native interacting and constructed reference solutions form the physical pair',
   'An original native empirical solution and natural one-copy equation construct the genuine independent reference cloud and their actual full paired local SDE, with all physical drift, diffusion, coordinate and simultaneous noise identities derived.',
   'Primitive Borel fields, original initial L2, the original native interacting solution and natural mean-field solution are explicit. A1 alone is not asserted to construct an arbitrary interacting system. No final coefficient, law, noise or raw paired-process compatibility is supplied.'),
})

MODULES.update({
 'NaturalFiniteWorkContraction': ('Original constant-diffusion contraction under finite signed A3 work',
   'Natural original local equations, Dirac coercivity and universal finite signed work derive original moments, positive-work integrability, Fubini and exact realised RMS and pair-law contraction.',
   'FiniteCouplingWork is independent of the conditional inequality and is the stated ordinary finite-integral interpretation. Original local equations, constant columns, positive A3 rate and primitive Borel fields are explicit. No A4, response continuity, norm growth, global moment, work estimate or energy conclusion is supplied.'),
 'NaturalFiniteWorkLaw': ('Genuine initial Wasserstein contraction under finite signed work',
   'Every actual initial coupling receives natural canonical original trajectories and the same Brownian Driver; proved original equations and laws give the infimum contraction.',
   'Canonical actual strong-solution instances, constant diffusion, A3 and the unconditional finite signed-work convention remain explicit. Realisation, marginal laws, stochastic matching, positive work, moments and final transport estimates are derived.'),
 'NaturalFiniteWorkArbitraryLaw': ('Finite-signed-work source contraction across arbitrary original sources',
   'Actual Wiener-path law uniqueness identifies two original raw solutions with their canonical counterparts. The proved finite-work comparison yields the exact optimal initial Wasserstein factor.',
   'Original raw equations, direct A1 canonical/path strong-existence instances and same-driver uniqueness, primitive Borel fields, positive A3 and independent FiniteCouplingWork are explicit. No ambient separability, A4, response continuity, drift-norm growth, work or energy premise is imposed. Extended-negative work is outside this convention.'),
 'RawSamplerCoerciveMoment': ('Natural Dirac contractivity derives original uniform sampler moments',
   'Primitive weighted Dirac monotonicity gives compact drift anchors and coercivity. Genuine stopping, computed local energy and Fatou derive uniform original second moments and product-time square integrability.',
   'Natural original sampler equations, Borel projected drift, positive A3 rate and constant diffusion are explicit. FiniteCouplingWork, global drift moments, norm growth and an expected-energy conclusion are unnecessary.'),
 'RawReferenceCloudData': ('The actual independent physical cloud solves its original local equation',
   'One natural mean-field sampler constructs the full independently seeded physical cloud, its literal original local SDE and controlled raw representation.',
   'Primitive Borel projected drift and original one-copy raw equation are inputs. Product Driver, joint continuous representative, physical columns, coefficient/noise and state identities are proved. No supplied iid law or cloud equation is assumed.'),
 'RawEmpiricalDynamics': ('The native finite-average empirical stochastic equation',
   'The time-dependent model encodes the literal finite-average response, a shared random optimizer and physical sampler noise with zero optimizer diffusion. Natural original solutions yield controlled raw data.',
   'An actual original interacting solution and initial L2, together with primitive Borel observation/drift/response maps, are explicit. Arbitrary finite-particle existence is not inferred from mean-field A1, and no final pair law or error is supplied.'),
 'RawConstructedParticleBounds': ('Sharp source interaction bound for the original native particle system',
   'The natural paired construction supplies all physical coefficients, common noise and original iid reference law internally; localized forcing and Fatou yield the exact empirical Wasserstein RMS floor on the original native solution.',
   'The actual interacting native solution lives on the constructed independent whole-seed product, with synchronous original initial coordinates. Positive N/rho, A3/A4/A5, actual original mean-field solution and primitive Borel fields are visible. No paired process, cloud law, noise matching, energy, global drift moment or final bound is assumed.'),
})

MODULES.update({
 'RawConstructedParticleParameter': ('Exact source parameter bounds for the original native empirical solution',
   'The actual independent reference cloud and physical particle/copy pair are constructed internally. True initial Wasserstein relaxation and the sharp local particle floor give the original parameter L2 bound in both A1 branches.',
   'An original native interacting solution on independent whole seeds, natural original mean-field equations, initial P2 and synchronous coordinates, primitive Borel maps, one-Lipschitz parameter projection, A3/A4/A5 and actual stationary target remain explicit. A1 supplies direct canonical/path strong-existence and uniqueness instances. The constant branch needs no universal finite work; the state-dependent branch uses primitive linear-growth regularity. No pair, noise/law compatibility, energy or final bound is supplied.'),
})

MODULES.update({
 'RawConstructedParticleJointLimit': ('Joint time/population convergence of the original native parameter errors',
   'For each population and observation horizon, the original empirical solution and primitive A1/A2 witnesses form a natural family. Both source branches derive the sharp original parameter bound before the product-filter limit is taken.',
   'Uniform response Lipschitz and reference observation variance, P2 laws, positive A3, primitive Borel fields, original native solutions and synchronous initialization are explicit. Family and Branch contain only equations, initial conditions, actual target stationarity and well-posedness/primitive-growth witnesses. No final error estimate, paired process, law matching, energy or work is a field; horizon-coherent global trajectories are included by restriction.'),
})

MODULES.update({
 'ContinuousFlowMeasure': ('Literal continuous source-flow Lebesgue preservation',
   'The source C1 field and actual global trajectories imply the flow group identity and negative-time inverse by ODE uniqueness. Derived differentiability and determinant one then give actual MeasurePreserving via Jacobian change of variables.',
   'Only the primitive C1 arbitrary force, actual all-real ODE and identity initial map are assumed for the phase theorem. No bijectivity, inverse, flow regularity, global original-force Lipschitz bound or measure/Jacobian-preservation conclusion is supplied. The generic divergence-free theorem has explicit zero trace.'),
})

MODULES.update({'MetricFactor': ('Constructed positive finite-dimensional metric factors',
                  'A positive symmetric metric operator is factored into a Euclidean linear map, with '
                  'inner-product and norm-comparison identities proved.',
                  'Assume the original finite-dimensional real Hilbert space and symmetric positive metric; no '
                  'factor, square-root operator or coercivity conclusion is supplied.'),
 'EmpiricalMetric': ('Source A3 gives a contracting empirical particle metric',
                     'Actual paired empirical-cloud couplings instantiate source A3. Finite-dimensional metric '
                     'factorization and L² lifting give drift dissipation on every random particle state, '
                     'transported by the actual coordinate equivalence.',
                     'Use source A3, positive particle count, finite-dimensional physical coordinates and the '
                     'literal drift-packing identity. No random-state dissipativity or numerical contraction '
                     'is assumed.'),
 'MethodLpEquivalences': ('Actual inverse physical and raw implementation L² coordinates',
                          'Continuous linear joining, splitting and particle packing are proved inverse on L². '
                          'The actual M-MFPO and HOL full drifts are identified under these maps.',
                          'Primitive ParticleForceData and the original model definitions suffice; no output '
                          'matching, drift identity or measure-law conclusion is supplied.'),
 'ImplementationMetric': ('Actual M-MFPO and HOL contracting metrics derived from A3',
                          'The empirical metric is transported to each literal raw implementation space using '
                          'proved inverse L² maps and the actual physical particle drift identities.',
                          'Finite-dimensional optimiser and sampler coordinates, primitive ParticleForceData '
                          'and source A3 are explicit. The metric factor, coercivity, random-state '
                          'dissipativity and all coordinate identities are conclusions.'),
 'UniformIntegralMoments': ('Derived uniform moments and exact integral-flow contraction',
                            'A one-unit Gronwall radius, constructed zero-start Picard restarts and drift '
                            'contraction derive global uniform reference moments. Local radii and square-root '
                            'temporal moduli are derived too.',
                            'Global Lipschitz drift, primitive weighted drift dissipativity, the original '
                            'continuous additive integral equation and Brownian square-root increment bounds '
                            'suffice. No reference moment estimate or stability recurrence is supplied.'),
 'UniformDiscrete': ('All-iteration error absorption under an explicit small-step condition',
                     'Exact-flow contraction and an affine local numerical defect give an absorbed recursion '
                     'and a uniform square-root-step strong error. Supporting chain and geometric-radius '
                     'inequalities are proved.',
                     'This generic lemma displays map updates, exact contraction, local defect and reference '
                     'radius explicitly. The method and final target clients derive all these premises from '
                     'primitive force regularity and source A3.'),
 'UniformStepSize': ('Explicit positive uniform-error step threshold',
                     'The threshold min(1,1/rho,(rho/(4(b+1)))² is positive and guarantees the two absorption '
                     'inequalities, including b=0.',
                     'Only positive rho, nonnegative b and a positive step below the threshold are used; no '
                     'stability conclusion is assumed.'),
 'MomentumUniformLocal': ('Actual Gaussian OBABO local error with square-root temporal regularity',
                          'The literal thermostat, force kick and drift coefficients give local consistency '
                          'and explicit affine initial-radius coefficients.',
                          'Primitive force Lipschitz regularity, actual component integral equations, the '
                          'displayed reference increments and physical half-noise identity are explicit. Later '
                          'modules derive these radii, increments and noise identities.'),
 'MomentumUniformDefect': ('OBABO affine local error from primitive integral data',
                           'One-step state and drift radii and increment moduli are derived from the actual '
                           'kinetic integral equation. The Gaussian-coupled local defect is explicitly affine '
                           'in the random initial norm.',
                           'Only global force Lipschitz regularity, nonnegative friction, the original '
                           'continuous integral equation and Brownian increment/half-noise primitives remain; '
                           'no local-error or moment conclusion is assumed.'),
 'MomentumUniform': ('Time-uniform actual OBABO strong discretisation error',
                     'Picard restarts and primitive drift dissipativity give exact contraction; affine local '
                     'errors and derived global reference moments are absorbed into a uniform sqrt(h) error.',
                     'The generic theorem displays metric coercivity and original drift monotonicity; final '
                     'particle clients derive them from source A3. No numerical contractivity, local defect, '
                     'moments or final recurrence are assumed.'),
 'MomentumUniformParticle': ('Actual independent-Gaussian M-MFPO all-iteration bound',
                             'Actual Brownian coordinate half-steps construct the Gaussian implementation '
                             'innovations, their norms and exact physical-input identity. The full-state error '
                             'is uniform over every iteration.',
                             'Primitive ParticleForceData, nonnegative friction, the original global integral '
                             'equation and metric drift dissipativity/coercivity are explicit here. '
                             'FullyUniformMomentum constructs the process and metric internally.'),
 'HOLUniformLocal': ('Printed HOL coefficients give absolute affine local remainders',
                     'The actual parameter-first endpoint-force scheme has an absolute local remainder growing '
                     'linearly in the input norm. Primitive force bounds also give a global full-drift '
                     'Lipschitz constant.',
                     'Separate global joint Lipschitz force conditions and physical coefficient signs suffice. '
                     'No Lipschitz remainder estimate or numerical contractivity is asserted.'),
 'HOLRestart': ('Constructed exact HOL restarts on the actual Brownian source',
                'Global Picard solutions, their original integral equations, physical Brownian increment '
                'radii, restart identity and primitive-metric contraction are proved.',
                'Separate force Lipschitz conditions and the actual measure-preserving Brownian source suffice '
                'for construction; contraction uses primitive drift dissipativity, derived from A3 in the '
                'final client.'),
 'HOLRestartLocal': ('Actual printed Gaussian HOL local error with derived radii',
                     'Original Picard integral equations and Brownian increments derive every local moment and '
                     'temporal modulus. The actual correlated-Gaussian local error is h sqrt(h) times an '
                     'affine function of the input norm.',
                     'Only primitive force regularity, alpha>0, gamma>=0 and the actual Brownian source are '
                     'supplied. No reference moment, drift modulus, local-error or numerical stability '
                     'conclusion is a premise.'),
 'HOLUniform': ('Time-uniform actual printed HOL strong discretisation error',
                'Constructed Picard restarts contract, their Gaussian local defects have explicit affine '
                'growth, and the original integral equation yields uniform reference moments. Small-step '
                'absorption gives the all-iteration sqrt(h) bound.',
                'The generic theorem displays primitive weighted drift dissipativity and metric coercivity, '
                'subsequently derived from source A3. Numerical contraction, local errors, uniform moments and '
                'error recurrences are not assumptions.'),
 'FullyUniformMomentum': ('Theorem New A: constructed time-uniform M-MFPO parameter bound',
                          'Source A3 constructs the contracting raw particle metric. The actual global '
                          'particle process, Gaussian coupling, uniform moments and affine local errors give a '
                          'positive fixed step threshold and all-iteration parameter bound.',
                          'Finite-dimensional physical coordinates, independent globally jointly Lipschitz '
                          'forces, nonnegative friction, positive N/rho, P2 initial/target laws, an actual '
                          'frozen invariant trajectory, zero target mean observation and A5 are explicit. No '
                          'metric, process, reference, moment, local defect or final recurrence is supplied. '
                          'Constants may depend on fixed N.'),
 'FullyUniformHigherOrder': ('Theorem New B: constructed time-uniform printed HOL parameter bound',
                             'The literal printed Gaussian implementation is compared with the actual '
                             'constructed particles in the A3 metric. Uniform moments and derived local errors '
                             'yield an all-iteration parameter bound below a positive fixed step threshold.',
                             'Finite-dimensional coordinates, separate globally jointly Lipschitz forces, '
                             'alpha>0/gamma>=0, positive N/rho, P2 initial/target laws, actual frozen '
                             'invariant trajectory, zero target mean observation and A5 are explicit. No '
                             'numerical contraction, reference moment, drift modulus, error recurrence or '
                             'matching-law conclusion is assumed. Constants may depend on fixed N.')})

MODULES.update({'MethodMetricComparisons': ('Numerical metric comparisons from exact shared L² coordinate identities',
                             'The physical particle norm squared equals the sum of all four raw component '
                             'second moments. The actual coordinate maps have norm at most two, and their '
                             'inverses at most one; source A3 therefore constructs a contracting factor with '
                             'explicit square-root metric bounds.',
                             'Only the standard Euclidean cloud encoding and primitive finite-dimensional '
                             'source metric/A3 are used. The comparison identities require no independence '
                             'of the shared coordinates. No operator-norm, numerical-contraction or moment '
                             'estimate is assumed.'),
 'UniformConstantExpansions': ('Closed arithmetic expressions for every new local-error coefficient',
                               'Direct algebra certifies the complete M-MFPO and HOL local constants, '
                               'including all nested coefficient, Gaussian and drift-Lipschitz terms. The '
                               'identities connect the human-readable formulas to the existing local-error '
                               'estimates.',
                               'The HOL simplifications require positive alpha and the displayed nonnegative '
                               'friction/Lipschitz constants; M arithmetic uses its nonnegative primitive '
                               'constants. These are proved equalities of definitions, without a supplied '
                               'estimate or new analytic assumption.'),
 'CloudEncodingConstants': ('Exact numerical norms of the standard Euclidean cloud encoding',
                            'The reindexing map has norm one and inverse norm sqrt(N) in positive dimension, '
                            'with explicit zero-dimensional cases. These identities give exact certified '
                            'force constants 2 ell_F and 2 sqrt(N) ell_x.',
                            'Positive particle count and the standard coordinate encoding are explicit. '
                            'Exact nonzero norms use Nonempty spatial index; the separate empty-index '
                            'statements cover dimension zero. No norm comparison is assumed.')})

MODULES.update({'UniformOriginConstants': ('Exact primitive force values for every uniform numerical coefficient',
                            'Actual constant L² identities reduce lifted zero-force norms to the primitive '
                            'F(0,0) and sqrt(N) G(0,0). The full raw kinetic and HOL drift norms at zero are '
                            'the maximum of those two values.',
                            'A probability source, positive particle count and the actual standard Euclidean '
                            'cloud encoding suffice. No zero-force identity, operator norm, independence or '
                            'numerical estimate is a premise.')})

def _pbgso_mask_lexical(source):
    """Mask comments/literals without changing source offsets or line breaks.

    The legacy teaching parser is deliberately untouched. In particular, a
    string or comment containing ``:=`` must not end a PBGSO theorem header.
    """
    out, index, block_depth, string, quoted_name = [], 0, 0, False, False
    while index < len(source):
        char, pair = source[index], source[index:index + 2]
        if block_depth:
            if pair == '/-':
                block_depth += 1; out.extend('  '); index += 2
            elif pair == '-/':
                block_depth -= 1; out.extend('  '); index += 2
            else:
                out.append('\n' if char == '\n' else ' '); index += 1
        elif string:
            if char == '\\' and index + 1 < len(source):
                out.append(' ')
                out.append('\n' if source[index + 1] == '\n' else ' ')
                index += 2
            else:
                out.append('\n' if char == '\n' else ' '); index += 1
                if char == '"':
                    string = False
        elif quoted_name:
            out.append('\n' if char == '\n' else ' '); index += 1
            if char == '»':
                quoted_name = False
        elif pair == '/-':
            block_depth = 1; out.extend('  '); index += 2
        elif pair == '--':
            end = source.find('\n', index)
            if end == -1:
                end = len(source)
            out.extend(' ' * (end - index)); index = end
        elif char == '"':
            string = True; out.append(' '); index += 1
        elif char == '«':
            quoted_name = True; out.append(' '); index += 1
        else:
            out.append(char); index += 1
    if block_depth or string or quoted_name:
        raise ValueError('Unterminated PBGSO Lean comment or literal')
    return ''.join(out)


def _pbgso_header_marker(masked, declaration):
    """Locate the actual body delimiter, not a nested named argument.

    ``marker_column`` is a zero-based offset in the ORIGINAL source line.
    Counting only lines is insufficient when ``(I := I)`` and the actual proof
    delimiter occur on the same line. A result type may also begin with one
    or more top-level ``let x := ...;`` terms; their assignments belong to
    the statement and are skipped. Equation-style declarations retain their
    preceding header line as the fallback boundary.
    """
    opening = {'(': ')', '[': ']', '{': '}', '⟨': '⟩', '⦃': '⦄'}
    closing = set(opening.values())
    stack, pending_lets, equation = [], 0, None
    for number in range(declaration['start'], declaration['end'] + 1):
        line, column = masked[number - 1], 0
        while column < len(line):
            char = line[column]
            if char in opening:
                stack.append(opening[char]); column += 1
            elif char in closing:
                if stack and stack[-1] == char:
                    stack.pop()
                column += 1
            elif line[column:column + 2] == ':=':
                if not stack:
                    if pending_lets:
                        pending_lets -= 1
                    else:
                        return number, column, ':='
                column += 2
            elif char.isalpha() or char == '_':
                word = re.match(r"[\w']+", line[column:])[0]
                if not stack:
                    if word in ('let', 'letI'):
                        pending_lets += 1
                    elif word == 'where' and not pending_lets:
                        return number, column, 'where'
                column += len(word)
            else:
                if char == '|' and not stack and equation is None:
                    previous = number - 1
                    equation = (previous, len(masked[previous - 1]), '')
                column += 1
    if equation is not None:
        return equation
    raise ValueError(f"Cannot locate PBGSO body of {declaration['name']} at {declaration['start']}")


def pbgso_declarations(source):
    """Retain namespace-distinct declarations sharing a short source name.

    Keep the last short key for existing main-page references; earlier
    collisions use their actual namespace-qualified source names. Only the
    parser input is changed: every displayed excerpt uses the original source.
    """
    lines = source.splitlines()
    # Parse inductive assumption alternatives with the same source boundaries
    # as structures, while retaining their actual keyword and complete source.
    inductives = set()
    for i, line in enumerate(HELPERS.mask_comments(lines)):
        if re.match(r'^(?:private |noncomputable )*inductive\b', line):
            inductives.add(i+1)
            lines[i] = re.sub(r'\binductive\b', 'structure', lines[i], count=1)
    masked = HELPERS.mask_comments(lines)
    scope, found, instances = [], [], 0
    for number, line in enumerate(masked, 1):
        if match := re.match(r'^namespace\s+([\w.]+)', line):
            scope.append(('namespace', match[1]))
        elif match := re.match(r'^section(?:\s+([\w.]+))?\s*$', line):
            scope.append(('section', match[1]))
        elif match := re.match(r'^end(?:\s+([\w.]+))?\s*$', line):
            if scope:
                scope.pop()
        if match := HELPERS.DECL.match(line):
            namespaces = [name for kind, name in scope if kind == 'namespace']
            qualified = '.'.join(namespaces + [match[2]])
            found.append((number, match[2], qualified, match.span(2)))
        elif re.match(r'^(?:local |noncomputable |private )*instance\b', line):
            instances += 1
    last = {name: number for number, name, _, _ in found}
    full_names = {}
    for number, name, qualified, (start, end) in found:
        full_names[number] = qualified
        if last[name] != number:
            lines[number-1] = lines[number-1][:start] + qualified + lines[number-1][end:]
    parsed = declarations('\n'.join(lines))
    assert len(parsed) == len(found) + instances, 'PBGSO declaration omitted by inventory parser'
    for declaration in parsed.values():
        declaration['lean_name'] = full_names.get(declaration['start'], declaration['name'])
        if declaration['start'] in inductives:
            declaration['kind'] = 'inductive'
        # Context commands following a declaration are not part of its body.
        # Retain them in shared_context rather than hiding namespace scope.
        for number in range(declaration['start']+1, declaration['end']+1):
            if re.match(r'^(?:namespace\s|section(?:\s|$)|end(?:\s|$))', masked[number-1]):
                declaration['end'] = number-1
                while declaration['end'] > declaration['start'] and not source.splitlines()[declaration['end']-1].strip():
                    declaration['end'] -= 1
                break
    # Override the legacy first-':=' heuristic only for PBGSO. The mask is
    # made from the original source, since namespace disambiguation above
    # may change the length of a declaration's first line.
    original_masked = _pbgso_mask_lexical(source).splitlines()
    for declaration in parsed.values():
        marker, column, token = _pbgso_header_marker(original_masked, declaration)
        declaration.update(marker=marker, marker_column=column, marker_token=token)
        suffix = original_masked[marker - 1][column + len(token):].strip()
        declaration['body_start'] = marker + 1 if suffix in ('', 'by') else marker
    return parsed


def source_inventory():
    paths = sorted(p.relative_to(ROOT).as_posix() for p in (ROOT / "PBGSO").rglob("*.lean"))
    if (ROOT / "PBGSO.lean").is_file():
        paths.insert(0, "PBGSO.lean")
    sources = {p: (ROOT / p).read_text() for p in paths}
    parsed = {p: pbgso_declarations(s) for p, s in sources.items()}
    return sources, parsed


def proof_page(path):
    return "PBGSO/exposition/proofs/" + Path(path).stem + ".html"


def module_note(path):
    key = Path(path).stem
    if key in MODULES:
        return MODULES[key]
    raise ValueError(f'Missing PBGSO module explanation and assumption note: {path}')


def header_lines(source, decl):
    """Exact source rows through the complete statement, excluding its body."""
    rows = source.splitlines()[decl["start"] - 1:decl["marker"]]
    rows[-1] = rows[-1][:decl['marker_column']].rstrip()
    return rows


def header_text(source, decl):
    return "\n".join(header_lines(source, decl))


def exact_header(path, name, sources, parsed, page):
    decl = parsed[path][name]
    headers = dict(sources)
    rows = sources[path].splitlines()
    rows[decl["marker"] - 1] = header_lines(sources[path], decl)[-1]
    headers[path] = "\n".join(rows)
    context = context_text(sources[path], parsed[path])
    shared = ('<details class="statement-context"><summary>Exact shared imports, variables and namespace context</summary>'
              '<p class="small">All module context commands are shown in source order, with declaration bodies omitted. '
              'The complete module on the linked proof page preserves their scope.</p>'
              + commands(context, 'context-' + anchor(Path(path).stem + '.' + name), 'Copy shared context') + '</details>')
    is_contract = decl['kind'] in ('structure', 'inductive') or (
        decl['kind'] in ('def', 'abbrev') and re.search(r':\s*Prop\b', header_text(sources[path], decl)))
    if is_contract:
        rendered = code(path, decl['start'], decl['end'], sources, page, 'contract', name)
    else:
        rendered = code(path, decl['start'], decl['marker'], headers, page, 'statement', name)
    # Short names may recur in different modules at the same source line.
    rendered = rendered.replace(' id="'+anchor(name), ' id="'+anchor(Path(path).stem+'.'+name))
    return shared + rendered


def source_docstring(source, start):
    prefix = "\n".join(source.splitlines()[:start - 1])
    match = re.search(r"/--([\s\S]*?)-/\s*$", prefix)
    if not match:
        return ""
    # The final immediately preceding comment, not an earlier declaration's comment.
    return match.group(1).rsplit("/--", 1)[-1].strip()


def context_text(source, parsed):
    covered = set()
    for decl in parsed.values():
        covered.update(range(decl["start"], decl["end"] + 1))
    return "\n".join(line for n, line in enumerate(source.splitlines(), 1) if n not in covered)


def assumption_inventory(sources, parsed):
    return {
        "schema_version": 1,
        "scope": "Exact syntactic theorem headers and complete declarations, with shared module context. "
                 "Structure fields, inductive alternatives and Prop definitions are included in full. Lean's elaborated theorem "
                 "types and transitive logical axioms are checked separately by PBGSO/Check.lean.",
        "modules": {
            path: {
                "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
                "scope_note": module_note(path)[2],
                "shared_context": context_text(source, parsed[path]),
                "declarations": {
                    name: {"kind": decl["kind"], "lean_name": decl["lean_name"],
                           "start_line": decl["start"], "end_line": decl["end"],
                           "exact_header": header_text(source, decl),
                           "exact_declaration": "\n".join(source.splitlines()[decl["start"]-1:decl["end"]])}
                    for name, decl in parsed[path].items()
                },
            } for path, source in sources.items()
        },
    }


PROSE = {
    "framework": r"""<p>Let \(S,\Theta,Z,X\) be independent optimiser, parameter, sampler and observed-state spaces. A finite noise index describes the columns of \(\sigma_\theta(z)\). Projections \(P_\theta:S\to\Theta\) and \(P_x:Z\to X\), an observation \(F:\Theta\times X\to\Theta\), an arbitrary optimiser response \(\Psi_t\), and sampler coefficients \(b,\sigma\) define</p>
<div class="equation">\[G_\nu(s)=\int F(P_\theta s,P_xz)\,\nu(dz),\qquad
\dot s_t=\Psi_t(s_t,G_{\nu_t}(s_t)),\qquad
dZ_t=b_{P_\theta s_t}(Z_t)dt+\sigma_{P_\theta s_t}(Z_t)dB_t.\]</div>
<p>The finite system uses \(G_{\nu^N}(s)=N^{-1}\sum_iF(P_\theta s,P_xZ^i)\), with \(N&gt;0\). The equality with the empirical-law integral is proved. Auxiliary optimiser variables and augmented sampler states are allowed; a common joint potential and equal parameter/sampler dimensions are unnecessary. The displayed optimiser equation has deterministic evolution; noisy-parameter IPLA requires an additional extension.</p>""",
    "source-assumptions": r"""<p>The source convergence results require all of the following conditions where indicated; they are not implied merely by choosing a sampler with the correct invariant distribution.</p>
<ol><li><strong>A1: well-posedness.</strong> Pathwise unique global finite-horizon mean-field strong solutions for deterministic optimiser initial states and sampler laws in \(\mathcal P_2\), preservation of second moments, and either constant diffusion or the stated linear growth bound. A finite-particle solution must also exist for results concerning that system.</li>
<li><strong>A2: stationary pair.</strong> Frozen invariance means an actual stationary weak frozen SDE realization on some probability space, retaining the complete sampler state; generator-only stationarity is insufficient. A critical point \(\nabla\ell(\theta_\star)=0\), an augmented state \(s_\star\) with \(P_\theta s_\star=\theta_\star\), \(\Psi_t(s_\star,0)=0\) for every nonnegative time, and a finite-second-moment frozen invariant sampler law with the required marginal. Despite its source label, this does not say global minimiser.</li>
<li><strong>A3: joint twisted contractivity.</strong> Positive definite optimiser and sampler quadratic weights give, for every pair of states, every two admissible laws and every coupling, the joint drift pairing plus half the squared weighted diffusion difference at most \(-\rho\) times the joint squared energy, with \(\rho&gt;0\).</li>
<li><strong>A4: gradient response.</strong> \(\Psi_t(s,\cdot)\) is uniformly \(L_\Psi\)-Lipschitz.</li>
<li><strong>A5: uniform fluctuations.</strong> Along the chosen mean-field path, \(\sup_t\mathbb E\|F(\bar\theta_t,P_x\bar Z_t)-G_{\bar\nu_t}(\bar s_t)\|^2\le V_F&lt;\infty\).</li>
<li><strong>Probability and integrability.</strong> Positive particle count, deterministic optimiser initial state, i.i.d. sampler initial states independent of independent Brownian drivers, synchronous paired coupling, and the actual observation/test domains stated in each theorem. Energy identities, localization moments and noise properties are derived by the actual-process results where claimed. Background integrability only under \(\pi_\theta\) does not establish observation domains for arbitrary comparison laws.</li></ol>
<p id="finite-signed-integrals"><strong>Finite signed-integral convention for A3.</strong> The low-level joint inequality is tested on couplings where its integrals exist. Separately, <code>FiniteCouplingWork</code> states that the signed sampler work is absolutely integrable for <em>every</em> joint probability law of finite quadratic moment, for every optimiser pair. This is the explicit ordinary finite-integral reading of the source’s universal A3 formula. The constant-diffusion source2 development uses this property; it is not inferred from the conditional inequality.</p>
<p>The convention is substantive. Lean constructs a P₂ law for which the strongly dissipative scalar drift \(b(z)=-z-z^3\) has nonintegrable signed work against zero. An extended-negative-work reading therefore covers more superlinear models. The projected criteria establish the joint inequality on their displayed integrability domains; they do not automatically certify universal finite work. A finite reading of the universal U5 signed integrals must likewise be stated explicitly when combining that criterion with the constant-diffusion law theorem.</p>""",
    "paper-rates": r"""<p>Writing \(d^2=\|s-\widetilde s\|^2+W_2^2(\nu,\widetilde\nu)\) and \(\kappa\) for the ratio of upper and lower metric eigenvalue bounds, the source establishes</p>
\[d_t\le\sqrt\kappa e^{-\rho t}d_0,\qquad
\|\theta_t^N-\theta_\star\|_{L^2}\le\sqrt\kappa e^{-\rho t}d_0+
\frac{L_\Psi}{\rho}\sqrt{\frac{\kappa V_F}{N}}(1-e^{-\rho t}).\]
<p>Its interaction estimate compares interacting particles with an independent-copy <em>empirical</em> law, not directly with the population law. A full empirical Wasserstein error needs an additional sampling term. Stationary uniqueness is restricted to finite-second-moment laws \(\delta_s\otimes\nu\). None of the source's continuous-time theorems establishes a method-specific time discretisation rate.</p>""",
    "energy": r"""<p>For a supplied continuous nonnegative energy with a right derivative, Lean proves the comparison from \(E'\le-2\rho E\), and the regularized square-root comparison from \(E(0)=0\) and</p>
\[E'(t)\le-2\rho E(t)+2c\sqrt{E(t)}\quad\Longrightarrow\quad
\sqrt{E(t)}\le\frac c\rho(1-e^{-\rho t}).\]
<p>The proof differentiates \(\sqrt{E+\varepsilon^2}\) and removes \(\varepsilon\), so it does not assume differentiability of \(\sqrt E\) at zero. Metric comparisons yield the \(\sqrt\kappa\) factor. A separate theorem derives the energy inequality from actual common-additive-input integral equations and transformed drift monotonicity. Another module proves the i.i.d. variance identity on the finite product law. WeakContraction separately derives the full state-dependent synchronous-generator energy identity from its actual quadratic test equation. LawContraction takes the infimum over genuine initial couplings and proves the exact optimiser–law distance contraction and stationary uniqueness. The actual constructed integral modules below derive synchronous law realizations in their explicit integrability class. These scalar and weak-generator statements are intermediate interfaces. The original raw-process theorems above derive their required calculus and physical reference assembly under the named source assumptions.</p>""",
    "momentum": r"""<p>For the concrete OBABO map, let \(e\) be the sum of position and momentum discrepancies, assume the coupled force is globally \(L\)-Lipschitz with \(L\ge0\), and let the thermostat satisfy \(|\eta|\le1\). With</p>
\[A=(1+|h|L/2)^2(1+|h|),\]
<p>the proved map estimate is</p>
\[e_{n+1}\le A e_n+|\sigma|\big(A\|\Delta\xi_n\|+\|\Delta\xi'_n\|\big).\]
<p>If each innovation discrepancy is at most \(\varepsilon\), the verified finite-step bound is \(e_n\le A^ne_0+|\sigma|(A+1)\varepsilon\sum_{j=0}^{n-1}A^j\). The recurrence is derived by composing the exact kick, drift and thermostat maps. These new bounds give robustness and finite-horizon stability; \(A\) can exceed one. They do not establish convergence to the optimum or invariant Gibbs law. The optimiser's noise coordinate is zero.</p>""",
    "integral-construction": r"""<p>For time-independent, globally Lipschitz observation, optimiser response and sampler drift maps, the code constructs actual finite-horizon integral solutions in a deterministic optimiser coordinate times an L² sampler coordinate. It also constructs an interacting-system L² solution using the actual finite average. A continuous additive sampler input is supplied; this does not construct a state-dependent Itô integral. The model definition and weak stationarity statements separately allow time-dependent optimiser responses.</p>
<p>For two continuous integral solutions with common additive input, a globally Lipschitz drift and a continuous linear transformation \(C\) into a Hilbert space, assume</p>
\[\rho\|C(y-z)\|^2\le\langle C(y-z),C(g(y)-g(z))\rangle.\]
<p>The derived difference equation proves \(\|C(Y_t-Z_t)\|\le e^{-\rho t}\|C(Y_0-Z_0)\|\), with the stated norm-comparison prefactor when converted back to the original norm. This theorem derives its energy derivative from the actual integral equations rather than assuming the final scalar differential inequality. A separate nonautonomous version allows time-dependent drift along supplied continuous integral solutions; it does not construct those solutions.</p>
<p>AdditiveJointBridge derives the lifted drift inequality directly from source A3 using the actual sampler-pair pushforward law, its marginals and weighted L² work identities. It then constructs both solutions and gives the exact Euclidean optimiser/L²-sampler contraction. Its model compatibility requires the displayed independent observation/sampler maps, an autonomous optimiser response and constant diffusion columns. It does not assume the requested lifted dissipation bound. The common continuous input is arbitrary; identifying a particular Brownian input K with that Model also requires its diffusion columns to equal sqrt(2) K e_i. AdditiveDiffusion constructs a normalized K from every finite constant diffusion family and proves this identity, together with the actual input scaling.</p>
<p>The Brownian-input module derives an L² square-root increment bound from given coordinate pre-Brownian laws and constructs mean-field integral solutions for any fixed linear diffusion map. Coordinate independence remains a separate hypothesis when needed for an SDE interpretation.</p>""",
    "momentum-consistency": r"""<p>A further new theorem compares the actual OBABO trajectory against compatible kinetic integral-solution segments. Assume the force is \(L\)-Lipschitz, \(h,L,\gamma\ge0\), \(|\eta|\le1\), grid momentum and force norms are bounded by \(P,F\), the first innovation norm is at most \(\Xi\), the reference momentum and position have increment norms at most \(R\sqrt t\) on each step, and the net thermostat increment differs from the reference additive increment by at most \(B\). These reference, moment, modulus and noise conditions are required only on the used segments \(k&lt;n\).</p>
<p>With \(\mathcal R\) the exact coefficient budget <code>momentumRemainderBudget</code>, the formal bound is</p>
\[e_n\le A^n e_0+\left(\mathcal R+B+\tfrac23(L+\gamma+1)Rh\sqrt h\right)\sum_{j=0}^{n-1}A^j.\]
<p>The local defect is proved by expanding the concrete map and integrating the reference modulus. All coefficient, force, momentum and innovation terms are explicit in the adjacent definitions and signature. The norms may themselves be L² norms, but Brownian existence, covariance coupling and the required moment/modulus estimates must be established for that stochastic application. The displayed bound keeps those assumptions and does not imply an optimal or uniform-in-time rate.</p>""",
    "momentum-rate": r"""<p>For the physical coefficients \(\eta=e^{-\gamma h/2}\), \(\sigma=\sqrt{1-e^{-\gamma h}}\), take \(L,\gamma\ge0\), \(0&lt;h\le1\), a globally \(L\)-Lipschitz force, compatible kinetic integral-reference segments, grid momentum and force bounds \(P,F\ge0\), a reference increment modulus \(R\sqrt t\), and bounds \(\|\xi\|,\|\xi'\|\le\Xi\). The reference full increment is explicitly matched to \(\sqrt{\gamma h}(\xi+\xi')\). Set</p>
\[K_M=1+2L+L^2/2,\qquad
D_M=\tfrac{\gamma^2+\gamma}{2}P+\tfrac{\gamma+1}{2}F+\tfrac L2(P+\Xi+F/2).\]
<p>The verified finite-horizon estimate is</p>
\[e_n\le e^{K_Mnh}\left[e_0+\left(D_M+\sqrt\gamma\,\Xi+
\tfrac32\gamma\sqrt\gamma\,\Xi+\tfrac23(L+\gamma+1)R\right)(nh)\sqrt h\right].\]
<p>The proof derives the damping and noise coefficient remainders, and bounds the net two-stage innovation mismatch by \(\tfrac32\gamma\sqrt\gamma\,\Xi h\sqrt h\). It does not assume a numerical error recurrence. The headline raw-particle L² theorem uses \(L=2\max(L_F,L_G)\), where \(L_F=\mathtt{D.meanLip}\) and \(L_G=\mathtt{D.samplerForceLip}\) are derived from the primitive force bounds and cloud encoding, and \(\Xi=\sqrt d\) for the full encoded cloud dimension. It uses actual normalized half increments. Their sum is identified with the scaled full Brownian increment, and their iid Gaussian sequence law requires independent coordinate grid paths. The reference integral equation and its force/momentum and modulus bounds remain explicit, only for \(k&lt;n\). Uniform bounds over meshes give the square-root-step rate on a fixed horizon.</p>
<p><strong>Actual raw-particle implementation.</strong> ParticleMethodLp constructs the empirical and sampler force lifts, proves their pointwise identities almost everywhere, and identifies the full OBABO map with the raw nonlinear particle step. The headline theorem applies the Gaussian bound to those proved lifts, including a shared random optimiser and zero optimiser innovations. A continuous linear cloud encoding with inverse is explicit; the supplied Euclidean encoding repacks the particle and spatial indices. The paper's independent isotropic particle innovations use the flattened index Fin(N)×J and that explicit Euclidean encoding. An arbitrary invertible encoding transforms the raw noise and does not automatically preserve isotropy. Reference integral equations and finite-horizon moments/moduli remain assumptions. No stationary-target or infinite-horizon claim is made.</p>""",
    "higher-order": r"""<p>HOL-MYPGD first takes an Euler parameter step, then applies the appendix's affine three-coordinate sampler update. Let \(G\) be its sampler force, globally \(L\)-Lipschitz in position uniformly over the parameter, and let \(h\ge0\). For the exact line force \(D=\int_0^hG(\theta,x+tu)dt\), Lean proves</p>
\[\|D-hG(\theta,x)\|\le\tfrac12L\|u\|h^2.\]
<p>Keeping the same initial state and innovation triple, the full-state discrepancy between endpoint and line quadrature is bounded by</p>
\[\left(h/2+1+|\mu_{31}|\right)\tfrac12L\|u\|h^2.\]
<p>This is a new verified local quadrature bound for the actual implemented endpoint choice. The comparison method uses the same affine response and exact line quadrature; it is not the exact SDE. Covariance validity, an infinite-horizon rate and convergence to the original unsmoothed optimum are separate questions.</p>""",
    "higher-order-consistency": r"""<p>The finite-horizon HOL theorem compares the actual appendix-coefficient map with compatible segments of the original higher-order additive integral equations. Assume separate joint sum-norm Lipschitz constants \(L_F,L_G\ge0\), \(h\ge0\), an integrable reference drift with increment modulus at most \(C\sqrt t\), optimiser force bound \(F_\theta\), sampler force bound \(F_G\) evaluated at the Euler-updated parameter, and auxiliary norm bounds \(U,V\). Its explicit noise premise is \(\|\xi_x\|+\|\xi_u\|+\|\xi_v-b\|\le B\), where \(b\) is the reference final-coordinate additive increment.</p>
<p>Let \(W=|h|/2+1+|\mu_{31}|\) and</p>
\[A_H=\max\!\left\{(1+|h|L_F)(1+W|h|L_G),\ |\mu_{12}|+|\mu_{22}|+|\mu_{32}|,\ |\mu_{13}|+|\mu_{23}|+|\mu_{33}|\right\}.\]
<p>The verified deterministic coefficient and splitting budget is</p>
\[\begin{aligned}
D_H={}&(h^2/2+|\mu_{31}h|)F_G
+(|\mu_{12}-h|+|\mu_{22}-1|+|\mu_{32}+\gamma h|)U\\
&+(|\mu_{13}|+|\mu_{23}-\gamma h|+|\mu_{33}-1+\alpha h|)V
+h^2L_GF_\theta.
\end{aligned}\]
<p>The full-state sum-norm error satisfies</p>
\[e_n\le A_H^n e_0+\left(D_H+B+\tfrac83Ch\sqrt h\right)\sum_{j=0}^{n-1}A_H^j.\]
<p>The map stability and local consistency inequalities are proved before this recurrence is summed. For a stochastic application, the moment/modulus bounds and the innovation/Brownian coupling must be instantiated. The supporting noise and covariance modules construct that coupling and identify the printed Gaussian law at positive physical parameters. The exact-budget bound alone does not assert a convergence order, uniform-in-time accuracy or a target-law bound; the next theorem adds the coefficient and noise estimates needed for a finite-horizon rate.</p>""",
    "higher-order-rate": r"""<p>The additional coefficient analysis gives an explicit finite-horizon square-root-step rate. Take \(\alpha&gt;0\), \(\gamma\ge0\), \(0&lt;h\le1\), and the nonnegative force, auxiliary and reference-modulus bounds from the preceding theorem. Let \(K_H\) be the computed stability constant and \(D_0\) the computed quadratic local consistency constant. If the local innovation discrepancy is at most \(C_\xi h\sqrt h\), the proved error estimate is</p>
\[e_n\le e^{K_Hnh}\left[e_0+\left(D_0+C_\xi+\tfrac83C\right)(nh)\sqrt h\right].\]
<p>Here \(C_\xi\) is a noise-coupling constant, distinct from the number of particles. The headline Gaussian-coordinate theorem substitutes its proved value directly, so it has no unknown noise-error premise. The coefficient remainders and \(A_H\le1+K_Hh\) are derived from the exact printed formulas, rather than postulated.</p>
<p>The canonical HOL noise construction proves a correlated Gaussian response triple coupled to an actual Brownian increment, its Gram covariance and independent time/spatial blocks. The covariance module identifies all six expanded manuscript entries with that Gram matrix and proves positive semidefiniteness. Brownian isometry supplies \(C_\xi=\sqrt d\,C_{\alpha,\gamma}\) with an explicit scalar constant. The compatible reference integral equation, force/auxiliary moments and drift modulus remain hypotheses, only for \(k&lt;n\). For convergence as \(h\to0\) at fixed horizon, the constants must be bounded uniformly over the chosen meshes. The printed response is still not the full exact force-free linear flow.</p>
<p><strong>Actual raw-particle implementation.</strong> The force lifts and full HOL one-step map are proved equal almost everywhere to the original nonlinear empirical and sampler updates, with a shared random optimiser. The headline theorem specializes the Gaussian estimate to those actual lifts; it has no force-identification or noise-error premise. The complete cloud dimension enters the Gaussian factor. The paper's independent isotropic particle noise uses the displayed flattened Euclidean encoding; arbitrary encodings transform the raw covariance. The reference integral/moment/modulus assumptions remain. This does not remove smoothing-target bias.</p>""",
    "coefficient-audit": r"""<p>An exact force-free fundamental matrix would satisfy \(\mu_{22}^\prime=\gamma\mu_{32}\). At \(\alpha=\gamma=h=1\), Lean proves that the printed coefficients instead have mismatch \(1-3e^{-1}\ne0\). This exact counterexample justifies retaining coefficient-error terms. It does not reject the numerical map or establish a replacement covariance law.</p>""",
    "model-limitations": r"""<p><strong>Hybrid smoothing.</strong> HOL-MYPGD samples from \(\pi_\theta^\lambda\propto e^{-E^\lambda}\) while observing the original \(F=\partial_\theta E\). For finite \(\lambda\), the equilibrium force can be biased relative to the original objective. A bound to its critical point must include a force/smoothing bias estimate.</p>
<p><strong>Printed HOL coefficients.</strong> The implemented affine coefficient matrix is not the exact full force-free linear flow: its printed coefficients fail \(\mu_{22}'=\gamma\mu_{32}\) for positive \(\alpha,\gamma,h\). The formal map uses those actual coefficients, with explicit consistency remainders. Its printed Gaussian covariance is identified with the response-kernel Gram matrix separately; this does not make the drift matrix the full exact flow.</p>
<p><strong>TV model.</strong> Standard image total variation is unchanged by adding a constant image. Hence \(\int_{\mathbb R^d}e^{-e^\theta\mathrm{TV}(x)}dx=\infty\). The source's assumed finite prior normaliser requires a repaired domain, anchoring or coercive penalty; the displayed full-space prior does not satisfy it. Repair can change the normalisation derivative and dimension term.</p>
<p><strong>Experimental claims.</strong> Neural EBM experiments do not establish global strong monotonicity, Lipschitz constants, the uniform variance bound or the hypocoercive friction threshold. The reported acceleration and reconstruction quality remain empirical observations. The source and formal-scope audit records these distinctions.</p>""",
}


def result_panel(title, prose, references, sources, parsed, math, page, identifier):
    body = f'<article class="proof-step" id="{identifier}"><h3>{E(title)}</h3><div class="pair"><div class="math-pane">' + math(prose) + '</div><div class="lean-pane">'
    for path, name in references:
        if path not in parsed or name not in parsed[path]:
            raise ValueError(f'Missing PBGSO main theorem: {path}: {name}')
        body += exact_header(path, name, sources, parsed, page)
        body += f'<p class="small"><a href="{relative(proof_page(path),page)}#{anchor(name)}">Complete proof and source context</a></p>'
    return body + '</div></div></article>'


def technical_document(sources, parsed, math):
    page = CATALOG
    body = ('<header class="hero"><div class="eyebrow">General stochastic optimisation · source-based formal development</div>'
            '<h1>PBGSO proof details and complete catalog</h1>'
            '<p class="subtitle">General optimiser responses and augmented sampler diffusions, with explicit analytic assumptions, '
            'proved comparison arguments and new bounds for the two implementation maps.</p>'
            '<p class="reference-notice"><strong>Source:</strong> Jiechen Jackie Zhang and O. Deniz Akyildiz, '
            '<em>Particle-based Generalised Stochastic Optimisation</em>, local manuscript. '
            'This page does not assign a publication venue or claim a published proof PDF.</p></header>'
            '<aside class="correspondence-note"><strong>Formal scope.</strong> The general model, actual Brownian/Itô integration, '
            'original stationary product laws, both source law-contraction branches, sharp original particle/parameter bounds, four appendix results and both actual particle-method bounds are proved. '
            'A2 means a stationary weak frozen SDE realization, not generator-only stationarity. A1 supplies full-system strong existence and same-driver uniqueness; '
            'actual path-space transport proves source stationarity across original probability spaces. No ambient measure separability is required. '
            'The constant-diffusion contraction uses the explicitly named ordinary finite signed-work reading of universal A3; an extended-negative-work theorem is not claimed. All eight numbered source statements and both actual method bounds are verified under these source interpretations. '
            'This finite-work convention is substantive and independent of the conditional joint inequality. Source A4/A5 derive target-comparison work without that convention. '
            'Both additive M-MFPO and HOL numerical endpoints construct their processes, Gaussian coupling, integral references and mesh-uniform constants. '
            'Primitive global joint Lipschitz force bounds for the methods, source A3, actual frozen invariance, P₂ laws and reference variance remain visible. '
            'The exact eight-result/two-method completion ledger below controls the strict verification result.</aside>'
            '<p><a href="index.html">Return to the theorem statements and proof roadmap</a>.</p>'
            '<nav class="jump-nav" aria-label="PBGSO technical contents"><a href="#framework">Framework</a>'
            '<a href="#assumptions">Assumptions</a><a href="#main-results">Formal results</a>'
            '<a href="#source-inventory">Paper correspondence</a><a href="#modules">Supporting proofs</a>'
            '<a href="#result-fully-constructed-momentum">M-MFPO bound</a><a href="#result-fully-constructed-hol">HOL bound</a>'
            '<a href="#verification">Verification</a></nav>' + toolbar())
    body += '<section class="section" id="framework"><h2>General framework</h2>' + math(PROSE['framework']) + '</section>'
    body += '<section class="section" id="assumptions"><h2>Source hypotheses and actual formal premises</h2>' + math(PROSE['source-assumptions'])
    body += '<p>Every supporting module below has a scope and assumption note. The <a href="assumption_inventory.json">exact assumption inventory</a> contains every current theorem header, full structure/definition contract and shared module context. The Lean panels are read from source at build time.</p></section>'
    body += '<section class="section" id="paper-results"><h2>Source continuous-time bounds</h2>' + math(PROSE['paper-rates']) + '</section>'
    body += '<section class="section" id="main-results"><h2>What the formal statements prove</h2>'
    body += result_panel('Source stationary product law from weak frozen invariance and A1',
        r'<p><strong>A2 has its SDE meaning.</strong> There is an actual stationary weak frozen sampler on some Brownian probability space, with its original locally constructed stochastic equation, continuous adapted paths, pathwise Bochner-L¹ drift and invariant P₂ output law. A generator-only invariant test identity does not supply this assumption. The frozen process need not be strong or live on the original solution’s source.</p>'
        r'<p><strong>A1 supplies the full coupled solution.</strong> Use its direct strong-existence instance on independent initial sampler law times the actual Wiener path law, and same-driver pathwise uniqueness on the proved valid Brownian filtrations. The initial/Wiener-path map, whole-path Gaussian laws, initialization independence, causal filtration transport and original local-noise naturality are all derived. Pulling this full-system solution to the frozen and original sources and applying uniqueness proves the literal stationary product law on the original source.</p>'
        r'<p>Zero mean observation, its integrability, the optimiser fixed point at every horizon time, the stationary initial sampler law and matching deterministic optimiser initial value remain explicit. The optimiser satisfies its original integral ODE. No growth, global drift moment, energy estimate, common-source frozen strong realization or final output-law equality is supplied.</p>',
        [('PBGSO/BrownianDriverPathLaw.lean','Driver.initialPathMap_measurePreserving'),
         ('PBGSO/BrownianPathDriver.lean','driver'),
         ('PBGSO/RawPathSolutionTransfer.lean','Data.law_eq_pathspace_solution'),
         ('PBGSO/RawPathSolutionTransfer.lean','stationary_product_law_of_weak_frozen')],
        sources, parsed, math, page, 'result-source-stationarity-pathspace')
    body += result_panel('Original linear-growth strong equations derive moments and true-law contraction',
        r'<p>The original simultaneous raw equation is driven by the actually constructed local Brownian integral. Its initial variable is L², and primitive linear growth bounds the drift plus the Euclidean column norm by \(K(1+P+\|X_t\|)\), with \(K,P\ge0\). The local energy controls raw drift variation and diffusion squares; genuine first-hit stops and capped computed martingales derive the stopped equations and all stopped moments.</p>'
        r'<p>Actual stochastic isometry and a Volterra argument yield a bound independent of the stopping threshold. Fatou then gives, for every \(t\le T\),</p>'
        r'\[\begin{gathered}\mathbb E\|X_t\|^2\le B_T,\\E_0=\mathbb E\|X_0\|^2,\\A=1+P^2,\\c_T=9K^2(T+1)T,\\B_T=e^{c_T}(3E_0+A)-A.\end{gathered}\]'
        r'<p>The original optimiser integral equation and continuous parameter projection derive a finite \(P\) on each horizon. Primitive growth and \(B_T\) then give actual spatial and product-time L² drift/diffusion. Genuine stopped-integral consistency proves that the original local noise equals the original global computed integral; every predictable Model datum and its literal sampler-law identity are constructed.</p>'
        r'<p>Actual path-space law uniqueness transfers canonical contraction to the original raw solutions on distinct probability spaces. Source A3 therefore proves the exact \(\sqrt\kappa e^{-\rho T}\) contraction with the <em>true optimal initial Wasserstein distance</em>. No global moment, L² coefficient curve, noise-matching, output-law or all-couplings-realization premise remains. Original coefficient measurability and model realization, observation domains, original optimiser equation and P₂ initial laws remain explicit. The superlinear constant-diffusion A1(i) branch does not follow from this growth proof.</p>',
        [('PBGSO/RawLinearGrowthState.lean','Data'),
         ('PBGSO/RawLinearGrowthState.lean','state_moment_le'),
         ('PBGSO/RawLinearGrowthState.lean','coefficients_square'),
         ('PBGSO/RawLinearGrowthState.lean','localNoise_eq_global'),
         ('PBGSO/OptimizerHorizonBounds.lean','exists_parameter_bound'),
         ('PBGSO/RawLinearGrowthModel.lean','Realization'),
         ('PBGSO/RawLinearGrowthModel.lean','predictableData'),
         ('PBGSO/RawLinearGrowthLaw.lean','law_distance_decay'),
         ('PBGSO/RawSamplerGrowthArbitraryLaw.lean','CanonicalSolution'),
         ('PBGSO/RawSamplerGrowthArbitraryLaw.lean','law_distance_decay')],
        sources, parsed, math, page, 'result-raw-linear-growth')
    body += result_panel('Source constant-diffusion law contraction: finite signed A3 integrals',
        r'<p>Use finite-dimensional complete Borel second-countable optimiser and sampler coordinates, with finitely many Brownian columns. Original solutions on two arbitrary Brownian probability spaces satisfy their original local stochastic equations and optimiser integral ODE. The sampler drift is only pathwise Bochner L¹; no drift-norm growth or time-L¹(L²) condition is imposed. Source A1 supplies its direct canonical and Wiener-path strong-existence instances plus same-driver uniqueness on the proved valid filtrations.</p>'
        r'<p><strong>The signed-integral convention is a visible premise.</strong> In addition to the conditional joint inequality, assume <code>FiniteCouplingWork</code>: for every optimiser pair and every joint probability measure with finite quadratic moment, the signed sampler coupling work is absolutely integrable. This is the ordinary finite-integral reading of the universal formula in A3. It has no observation-domain restriction.</p>'
        r'\[d_T\le\sqrt\kappa e^{-\rho T}d_0.\]'
        r'<p>Dirac monotonicity derives compact drift anchors and original uniform P₂ moments. Universal finite work derives compact-uniform positive sampler-work growth; Fubini and the actual constant-noise cancellation then give the energy comparison. Genuine initial couplings, local-noise transport and output laws are constructed, yielding the true initial Wasserstein infimum. No positive-work, moment, energy, stochastic matching or final law inequality is assumed. Primitive Borel coefficients and the original observation domains remain explicit.</p>'
        r'<p><strong>This scope does not include extended-negative-work A3.</strong> The verified scalar audit supplies a P₂ law for which the strongly dissipative drift b(z)=−z−z³ has nonintegrable signed work against zero. This is a scope witness, not a counterexample to the contraction conclusion. The theorem is verified under the named finite convention.</p>',
        [('PBGSO/DiracOptimizerGrowth.lean','FiniteCouplingWork'),
         ('PBGSO/RawSamplerCoerciveMoment.lean','natural_moments'),
         ('PBGSO/NaturalFiniteWorkArbitraryLaw.lean','CanonicalSolution'),
         ('PBGSO/NaturalFiniteWorkArbitraryLaw.lean','law_distance_decay'),
         ('PBGSO/FiniteWorkScopeAudit.lean','exists_p2_nonintegrable_work')],
        sources, parsed, math, page, 'result-constant-finite-work')
    body += result_panel('Constant diffusion: the exact additional positive-work condition',
        r'<p>The actual common constant Brownian input cancels from two original raw local equations. Their difference has an ordinary pathwise integral derivative even when the separate drifts are only pathwise L¹. Write the actual joint work as</p>'
        r'\[\begin{gathered}q_c(t,\omega)=\langle\Delta s_t,D_s\Delta\Psi_t\rangle\\{}+\langle\Delta Z_t,D_z\Delta b_t\rangle,\\ \int_0^T\mathbb E_c[(q_c)_+]\,dt&lt;\infty.\end{gathered}\]'
        r'<p><strong>This integrability condition is additional.</strong> It must hold for every genuine initial coupling c on its constructed common-Brownian realization. PositiveWorkFubini then derives full work integrability and expected quadratic balance; source A3 and Grönwall give the exact law contraction with the true initial Wasserstein factor. All original output-law and noise-cancellation identities are proved. No energy derivative or contraction conclusion is supplied.</p>'
        r'<p>This intermediate sufficient condition allows direct use of any separately proved one-sided work estimate. The preceding source theorem derives it from the named finite signed-integral convention; source A4 response Lipschitz and A5 reference variance also derive it for stationary-target comparison. Neither result assumes the final energy or law inequality.</p>',
        [('PBGSO/PositiveWorkFubini.lean','work_integrable'),
         ('PBGSO/RawConstantNoisePositiveLaw.lean','law_distance_decay'),
         ('PBGSO/RawNaturalConstantLawParameter.lean','parameter_bound')],
        sources, parsed, math, page, 'result-constant-positive-work')
    body += result_panel('Actual local integration and weak finite-variation quadratic calculus',
        r'<p>Joint raw diffusion fields have actual spatial L² sections, constructed integration, continuous martingale versions, exact weighted energy and valid coupling transport. First-hit localization uses the literal progressive path-energy integral. A single common null regularization handles almost-sure local integrability, and the actual local noise is glued from computed stopped integrals with simultaneous stopped identities.</p>'
        r'<p>Separate finite-variation theorems derive expected quadratic balance from original continuous paths, only pathwise Bochner-L¹ drift, actual computed noise and a square-integrable <em>random total-variation budget</em>. Strong Doob and genuine primitives construct every maximal radius and L² auxiliary variable internally. Product drift-work integrability and the integral energy family at every earlier time are derived. No time-L¹(L²) drift, martingale, stochastic-isometry, radius or final energy conclusion is supplied to these final computed statements.</p>'
        r'<p>The source results above use this actual calculus with derived local gauges and moments. The optional one-sided positive-work criterion remains available independently of the finite signed-integral convention; every theorem retains its actual domain explicitly.</p>',
        [('PBGSO/RawLocalIntegral.lean','RawLocalDiffusion'),
         ('PBGSO/RawLocalIntegral.lean','localNoise_stopped'),
         ('PBGSO/RawLocalRegularization.lean','RawLocalDiffusion.exists_of_ae'),
         ('PBGSO/DoobStrongL2.lean','finite_grid'),
         ('PBGSO/ConstructedRandomVariationIntegral.lean','energy_integral'),
         ('PBGSO/ConstantNoiseWork.lean','frozen_drift_le')],
        sources, parsed, math, page, 'result-localized-weak-energy')
    body += result_panel('Sharp particle interaction for the original raw local SDE',
        r'<p>The original interacting/copy state solves its actual finite-column local Brownian equation with the literal physical drift and diffusion. Genuine first-hit localization and explicit after-stop damping derive integrable energy families. The original reference cloud’s iid law supplies exactly variance/N; it is not imposed on the interacting variables or the artificially damped cloud. Fatou then removes the localization threshold and gives the original empirical Wasserstein bound:</p>'
        r'\[\begin{gathered}\left(\mathbb E\,d_{\rm emp}(P_T,\bar P_T)^2\right)^{1/2}\le c_N(1-e^{-\rho T}),\\ c_N=\frac{L_\Psi}{\rho}\sqrt{\frac{\kappa V}{N}}.\end{gathered}\]'
        r'<p><strong>Visible assumptions.</strong> Positive N and rho, source A3, source A4 response Lipschitz, source A5 uniform original reference observation variance, original reference iid marginal and deterministic reference optimiser, synchronous initial coordinates, initial L², continuous adapted raw paths, joint coefficient measurability and pathwise local drift/diffusion energy. Physical coefficient identities and the simultaneous original local equation are explicit process assumptions. The energy, work integrability, stopped identities, diffusion isometry, empirical-statistic measurability and final bound are derived. There is no global drift L², linear-growth or weak-generator test-domain premise.</p>'
        r'<p>Independent complete source seeds construct genuine product Brownian drivers, coordinate reference SDEs and iid marginal cloud laws. Actual bounded-linear and index-injection noise transport derives the full physical packed-cloud equation. The final theorem below instantiates the natural physical pair internally; no stochastic equation is inferred from an iid fixed-time law.</p>',
        [('PBGSO/RawParticleInteraction.lean','Data'),
         ('PBGSO/RawParticleInteraction.lean','forced_energy_bound'),
         ('PBGSO/RawParticleInteraction.lean','finite_particle_interaction_bound'),
         ('PBGSO/RawIndependentCopies.lean','cloud_law'),
         ('PBGSO/RawIndependentCopies.lean','coordinate_equations'),
         ('PBGSO/RawReferenceCloudEquation.lean','equation')],
        sources, parsed, math, page, 'result-raw-particle-interaction')
    body += result_panel('Source particle bound for the actual original empirical implementation',
        r'<p>The inputs are a natural one-copy mean-field solution U and an actual original native empirical solution Y on the independent whole-seed product probability space. Y uses the literal finite-average response, the shared random optimiser and the original physical diffusion columns. Positive particle count, initial L² and synchronous original initial coordinates are explicit; mean-field A1 alone is not asserted to construct an arbitrary particle solution.</p>'
        r'<p>Primitive Borel observation, projected drift and response maps construct the independent reference trajectories, valid full product Brownian Driver, physical Hilbert cloud, original packed SDE and actual interacting/reference pair. Every drift, diffusion, state, simultaneous-noise and iid-reference-law identity is proved. Source A3, source A4 response Lipschitz and source A5 original observation L²/variance then give exactly the displayed sharp empirical floor on <em>the original Y</em>.</p>'
        r'<p>There is no supplied paired raw process, iid-cloud identity, physical-coefficient matching, noise equation, global drift moment or final energy/error premise. The distance is the actual empirical-law Wasserstein statistic, whose measurability and coupling bound are proved. This is the synchronous independent-seed construction specified by the source.</p>',
        [('PBGSO/RawEmpiricalDynamics.lean','Solution'),
         ('PBGSO/RawConstructedParticleCopy.lean','build'),
         ('PBGSO/RawConstructedParticleBounds.lean','original_finite_particle_interaction_bound')],
        sources, parsed, math, page, 'result-original-particle-interaction')
    body += result_panel('Source parameter error for the original native implementation',
        r'<p>For the actual original Y, both source alternatives give the exact parameter bound</p>'
        r'\[\begin{gathered}\|P_\theta Y_T-P_\theta s_\star\|_{L^2}\\\le \sqrt\kappa e^{-\rho T}d_0\\{}+c_N(1-e^{-\rho T}),\\d_0^2=\|s_0-s_\star\|^2\\{}+W_2(\nu_0,\nu_\star)^2,\\c_N=\frac{L_\Psi}{\rho}\sqrt{\frac{\kappa V}{N}}.\end{gathered}\]'
        r'<p><strong>Visible process and target assumptions.</strong> An actual native empirical solution Y on the independent whole-seed product, a natural mean-field solution U, P₂ initial/target laws, synchronous original initialization, primitive Borel fields, a one-Lipschitz parameter projection, positive N/rho, A3/A4/A5 and an actual constant stationary target solution. Source A1 is used through its direct canonical/path strong-existence instances and same-driver uniqueness. The target stationarity is the original SDE assertion proved from A2 above, with zero mean observation and optimiser fixed point, rather than a generator-only condition.</p>'
        r'<p>The constant-diffusion branch derives target positive work from A4 and reference variance; it does <em>not</em> require universal FiniteCouplingWork. The state-dependent branch assumes the original primitive linear-growth/Borel/progressive regularity and derives global moments and stochastic realization. Every independent reference law, physical pair equation, original parameter identity, true initial infimum and L² triangle is proved. No paired process, iid interacting law, work/energy estimate, coefficient/noise matching or final rate is a premise. The target is the source critical point; minimization requires a separate assumption.</p>',
        [('PBGSO/RawConstructedParticleParameter.lean','original_parameter_bound_constant'),
         ('PBGSO/RawConstructedParticleParameter.lean','original_parameter_bound_linearGrowth')],
        sources, parsed, math, page, 'result-original-parameter')
    body += result_panel('Joint large-time and large-population limit for the original parameters',
        r'<p>For every population n+1 and requested finite horizon, Family contains actual original native empirical and mean-field equations, their synchronous initial coordinates, the direct A1 strong-existence/uniqueness instances and an actual stationary target. Branch is either constant diffusion or the primitive linear-growth regularity alternative. It contains no estimate, energy, work, paired process or output-law conclusion.</p>'
        r'\[\begin{gathered}\|P_\theta Y_t^{n+1}-P_\theta s_\star\|_{L^2}\longrightarrow0\\\text{as }(n,t)\to(\infty,\infty).\end{gathered}\]'
        r'<p>Uniform source A4 response Lipschitz and A5 reference variance, positive A3 rate, P₂ initial/target laws, target observation integrability, primitive Borel fields and a one-Lipschitz parameter projection yield this actual parameter-error limit. Each sharp endpoint bound is proved internally before the joint product-filter limit. This implies the source iterated-limit assertion. Coherent global original trajectories are included by restriction to the requested horizon; no separate final-bound interface is assumed.</p>',
        [('PBGSO/RawConstructedParticleJointLimit.lean','Family'),
         ('PBGSO/RawConstructedParticleJointLimit.lean','Branch'),
         ('PBGSO/RawConstructedParticleJointLimit.lean','parameter_joint_limit')],
        sources, parsed, math, page, 'result-original-parameter-limit')
    body += '<h3>Supporting comparison and realization interfaces</h3><p>The original source results above derive their actual stochastic calculus and process assembly. The following earlier interfaces retain their own equation, test-domain and integrability contracts; their module-specific conditions are not open obligations in the completed source ledger.</p>'
    body += result_panel('Weak stationarity from a frozen sampler',
        '<p>The constant candidate solves the explicit optimiser ODE and generator forward equation. Given uniqueness of that weak formulation, every solution with the same initial state and law is constant. Integrability, frozen generator stationarity, zero mean observation and the optimiser fixed point are explicit inputs.</p>',
        [('PBGSO/Framework.lean','stationary_of_frozen')], sources, parsed, math, page, 'result-stationarity')
    body += result_panel('Stationary product law from actual integral equations',
        r'<p>The sampler satisfies an actual pathwise drift-integral equation retaining arbitrary state- and parameter-dependent diffusion. A supplied frozen invariant trajectory, zero mean observation and optimiser fixed point construct the constant-optimiser candidate. Same-driver pathwise uniqueness then proves that the full output law is literally the Dirac optimiser tensor frozen sampler law.</p>'
        r'<p><strong>The integral interpretation is explicit.</strong> The operator J and admissible process class C are supplied by the implementation. Both the candidate and compared process satisfy C, and uniqueness is restricted to that same class; no Itô or adaptation implementation is constructed in this result. The hypotheses include the actual frozen trajectory and its constant output law, finite second moment, observation integrability, the optimiser fixed point at every nonnegative time, pathwise uniqueness for the displayed equations, and matching initial variables. The explicit class C can encode adaptedness, initial-noise independence and integrand admissibility; instantiating J, C and their uniqueness from source A1 remains an obligation. These are equation-level stationarity proofs; their intended Itô/process interpretation remains separate.</p>',
        [('PBGSO/IntegralStationarity.lean','SamplerIntegral'),
         ('PBGSO/IntegralStationarity.lean','IsMeanFieldIntegralSolution'),
         ('PBGSO/IntegralStationarity.lean','IntegralPathwiseUniqueness'),
         ('PBGSO/IntegralStationarity.lean','integral_stationary_product_law')],
        sources, parsed, math, page, 'result-integral-stationarity')
    body += result_panel('Stationarity and same-initial uniqueness for the computed integral',
        r'<p>The frozen sampler satisfies the original equation driven by the actually constructed predictable Brownian integral, with actual invariant output law. Zero mean observation and the optimiser fixed point construct the constant-optimiser model trajectory. Same-initial uniqueness proves its literal Dirac optimiser tensor sampler stationary law. Source A3 independently derives that uniqueness in this class, without requiring a positive contraction rate merely for uniqueness.</p>'
        r'<p><strong>Exact scope.</strong> The sampler drift is Bochner L¹ in time with L² values, diffusion is adapted time-L², and observation integrability, measurable model coefficients and genuine Driver properties are explicit. No arbitrary stochastic operator or stochastic-energy conclusion is assumed. Source A2 supplies actual frozen invariance; it is not inferred from a formal density cancellation. The later raw linear-growth theorem derives this realization from original local equations in A1(ii); the alternative superlinear constant-diffusion contraction remains separate, while the later original local path-space theorem proves stationarity from actual weak frozen SDE invariance.</p>',
        [('PBGSO/ConstructedStationarity.lean','FrozenSamplerData'),
         ('PBGSO/ConstructedStationarity.lean','stationary_product_law'),
         ('PBGSO/ConstructedUniqueness.lean','dataUniqueness_of_twisted')],
        sources, parsed, math, page, 'result-constructed-stationarity')
    body += result_panel('Stationary product law for the original locally integrable strong equation',
        r'<p>The stochastic noise is the actual constructed local Brownian integral of the original finite diffusion columns. The sampler has continuous adapted paths and merely pathwise Bochner-L¹ drift; no time-L¹(L²) drift, linear growth or expected-energy hypothesis is imposed. The optimiser obeys its original integral ODE with an integrable field, allowing time-measurable responses.</p>'
        r'<p>Source same-driver uniqueness, an <em>actual frozen invariant sampler trajectory on that Driver</em>, zero mean observation and the optimiser fixed point construct the constant candidate and prove the literal stationary product law. The frozen law’s normalization and P₂ follow from its actual initial L² variable.</p>'
        r'<p><strong>Realization is explicit.</strong> The compared sampler and frozen sampler must have the same initial random variable almost surely. The common-Driver condition belongs to this intermediate theorem. The following actual Wiener-path transfer proves the source stationarity assertion from a stationary weak frozen sampler on another source and the direct A1 full-system strong-solution instance; a common-source frozen strong solver is unnecessary.</p>',
        [('PBGSO/RawLocalStationarity.lean','SamplerData'),
         ('PBGSO/RawLocalStationarity.lean','Data'),
         ('PBGSO/RawLocalStationarity.lean','PathwiseUniqueness'),
         ('PBGSO/RawLocalStationarity.lean','FrozenSamplerData'),
         ('PBGSO/RawLocalStationarity.lean','stationary_product_law')],
        sources, parsed, math, page, 'result-raw-local-stationarity')
    body += result_panel('Full multiplicative weak-generator contraction and optimal law distance',
        r'<p>The actual synchronous pair generator acts on the twisted quadratic separation test. Its diffusion term is the squared difference of the full state- and parameter-dependent diffusion columns. The weak forward equation and optimiser ODE derive the energy derivative; no final dissipation or transport bound is assumed.</p>'
        r'\[\begin{gathered}E_t\le e^{-2\rho t}E_0,\\d_t\le\sqrt\kappa e^{-\rho t}d_0,\\d^2=\|s-s^\prime\|^2+W_2^2(\nu,\nu^\prime).\end{gathered}\]'
        r'<p><strong>Exact analytic premises.</strong> Supply actual marginal weak solutions, a synchronous pair forward equation, finite second moments, observation/test/generator integrability, and membership of the quadratic separation test in the generator domain. The law theorem requires such a synchronous realization with the same specified marginal trajectories for <em>every</em> genuine initial coupling. Arbitrarily approximating couplings prove the infimum bound; optimal-coupling attainment is unnecessary. The actual Euclidean product-law W2 is proved equal to the displayed component metric, using literal Dirac optimiser tensor sampler laws and lifted/projected measure couplings; that identity is not assumed. Positive rho then proves equality of two stationary optimiser states and sampler laws. The additive construction below proves the required law-preserving realization for autonomous constant-diffusion dynamics and common continuous input on the quadratic domain. This intermediate generator theorem retains its specified domain and realizability inputs. The original raw-process results above derive actual stochastic realizations under their stated A1 alternatives; no richer marginal generator domain is needed for those proofs.</p>',
        [('PBGSO/WeakContraction.lean','energy_decay'),
         ('PBGSO/LawContraction.lean','weak_law_contraction'),
         ('PBGSO/ProductTransport.lean','wasserstein_product_eq'),
         ('PBGSO/ProductTransport.lean','weak_product_law_contraction'),
         ('PBGSO/LawContraction.lean','stationary_weak_laws_unique')],
        sources, parsed, math, page, 'result-weak-laws')
    body += result_panel('Constructed integral solutions and actual drift contraction', PROSE['integral-construction'],
        [('PBGSO/GeneralProcess.lean','exists_integral'),
         ('PBGSO/AdditiveJointBridge.lean','AdditiveModelCompatibility'),
         ('PBGSO/AdditiveJointBridge.lean','exists_additive_model_contracting_pair'),
         ('PBGSO/LawContraction.lean','exists_contracting_pair_laws'),
         ('PBGSO/AdditiveContraction.lean','additive_integral_contraction_with_condition_number'),
         ('PBGSO/NonautonomousContraction.lean','nonautonomous_additive_integral_contraction'),
         ('PBGSO/BrownianProcess.lean','exists_brownian_integral'),
         ('PBGSO/Sampling.lean','gradient_sampling_rms_le')], sources, parsed, math, page, 'result-integral')
    body += result_panel('Constructed global additive processes and actual quadratic weak realization',
        r'<p>Primitive global Lipschitz maps and a continuous sampler input starting at zero construct a global norm-continuous optimiser/L²-sampler integral process. Finite Picard solutions are glued using proved common-input uniqueness. Its actual optimiser ODE, pushforward sampler laws, finite second moments and observation integrability are derived. The synchronous pair quadratic forward equation follows from the actual common-input cancellation.</p>'
        r'<p><strong>The generator domain is explicit.</strong> The constructed marginal test family is exactly empty and the pair test family is the singleton quadratic separation test. This is enough for the proved coupling-energy calculation; it does not assert the full marginal Itô/Fokker–Planck equation on arbitrary test functions. The model response is autonomous and diffusion columns constant. AdditiveDiffusion constructs the normalized finite-column diffusion map and proves its exact Brownian scaling, so no matrix-matching premise is needed for that constructed input. An arbitrary supplied input still needs its model interpretation. A measure-preserving L² pullback preserves the actual primitive field, integral solution and sampler law; no force or law equality is assumed in that change-of-space result.</p>',
        [('PBGSO/AdditiveWeakRealization.lean','exists_global_additive_integral_solution'),
         ('PBGSO/AdditiveWeakRealization.lean','isCoupledWeakSolution_quadratic'),
         ('PBGSO/LpPullback.lean','integral_solution_pullback'),
         ('PBGSO/LpPullback.lean','lpPullback_law')],
        sources, parsed, math, page, 'result-additive-realization')
    body += result_panel('Constructed additive laws contract over all initial couplings',
        r'<p>Each actual global marginal trajectory is selected once on its initial-law times noise probability space. For every genuine initial coupling, the two measure-preserving projections pull those fixed processes to initial-coupling times noise space. Their output marginals are proved unchanged, their sampler inputs coincide, and the initial joint law is exactly the supplied coupling.</p>'
        r'<p>Source A3 and the derived quadratic forward equation therefore prove the optimal optimiser–Wasserstein contraction for the constructed law trajectories. There is no assumed output-law identity or all-couplings realization in the final theorem. Primitive maps are globally Lipschitz, the response autonomous, diffusion columns constant and the input common and continuous from zero. The marginal test domain remains empty and the pair domain the quadratic singleton; the model Brownian input can be constructed with exact coefficient matching, while adaptation, richer marginal Itô equations and frozen target invariance remain separate.</p>',
        [('PBGSO/AdditiveCanonicalRealization.lean','realize_all_initial_couplings'),
         ('PBGSO/AdditiveCanonicalRealization.lean','constructed_law_contraction')],
        sources, parsed, math, page, 'result-additive-canonical')
    body += result_panel('Actual frozen trajectories construct the additive stationary target',
        r'<p>The frozen sampler input is an actual continuous L² trajectory with its original integral equation and constant output law, expressing the source frozen invariance assumption. Zero mean observation and the optimiser fixed point derive the complete constant-optimiser mean-field solution. Primitive common-input uniqueness proves that the canonical target process is stationary.</p>'
        r'<p>The all-initial-coupling construction then builds the full stationary-target data used by the parameter theorem; no target realizer, relaxation estimate or final output-law identity is assumed. Primitive Lipschitz maps, autonomous response, constant diffusion compatibility, positive source A3 and a one-Lipschitz parameter projection remain explicit. Marginal tests are empty, but actual frozen invariance is a substantive process input rather than a conclusion drawn from an empty test family.</p>',
        [('PBGSO/AdditiveStationaryTarget.lean','FrozenTrajectory'),
         ('PBGSO/AdditiveStationaryTarget.lean','canonical_target_stationary'),
         ('PBGSO/AdditiveStationaryTarget.lean','stationaryParameterData')],
        sources, parsed, math, page, 'result-additive-stationary')
    body += result_panel('Quadratic energy derived from an actual martingale residual',
        r'<p>For a norm-continuous L² process, subtract its initial value and actual Bochner drift integral. If this residual has a standard martingale representative and the displayed weighted diffusion-increment isometry, conditional expectation proves orthogonality to the adapted earlier state. Exact quadratic increments and limiting remainders derive the expected energy derivative.</p>'
        r'<p>The state, drift and finite diffusion columns are norm-continuous, the state is adapted, and the metric weight is symmetric. No expected-energy derivative or weak forward equation is supplied. The weighted increment isometry is an explicit stochastic-integral property; constructing the intended multiplicative Itô integral and deriving its martingale/isometry hypotheses remain separate.</p>',
        [('PBGSO/QuadraticMartingale.lean','expected_energy_hasDerivWithinAt')],
        sources, parsed, math, page, 'result-quadratic-martingale')
    body += result_panel('Constructed vector Itô integration for time-L² adapted columns',
        r'<p>Actual predictable Brownian sums derive the finite martingale and weighted isometry identities. Their literal time-L² embeddings complete on the closed range of all genuine adapted steps. Past translation averages, Fubini identification and continuous adapted approximants prove that every horizon time-L² column family with current-past AE measurability belongs to this domain, including every interval cut.</p>'
        r'<p>The computed integral has a standard adapted square-integrable martingale representative, exact weighted increment moments, zero initial value, actual L²-time continuity, subtraction, and measure-preserving source/valid-filtration transport. No diffusion time continuity, supplied approximation, stochastic isometry or martingale conclusion is required.</p>'
        r'<p><strong>Scope.</strong> These are actual constructed integrals for time-L² adapted columns. The general source A1 solution class still needs its intended strong-SDE/process-class identification and moment/localization transfer. L²-time continuity alone is insufficient for sample-path continuity; the later explicit Brownian-modification and maximal-limit construction proves simultaneous continuous versions of these actual computed integrals.</p>',
        [('PBGSO/PredictableStepDensity.lean','timeCut_mem_closedStep'),
         ('PBGSO/PredictableCurveIntegral.lean','predictableCurveIntegral_martingale'),
         ('PBGSO/PredictableCurveIntegral.lean','predictableCurveIntegral_increment_isometry'),
         ('PBGSO/PredictableIntegralTransport.lean','predictableCurveIntegral_pullback_enlarge')],
        sources, parsed, math, page, 'result-predictable-completion')
    body += result_panel('Actual selected additive trajectories are adapted',
        r'<p>The Picard problem is constructed inside each complete past-measurable L² subspace. The pointwise lifted nonlinear field preserves that subspace. Clamping the original input to the fixed past and using actual common-input uniqueness identifies this constructed trajectory with the selected original solution. No conditional projection is assumed to commute with a nonlinear drift.</p>'
        r'<p>The canonical initial sampler and the independent complete particle initial cloud are measurable in their actual constructed initial/noise filtrations. Their physical Brownian inputs are identified exactly with the Driver inputs and proved adapted. The actual selected canonical mean-field sampler and interacting particle realization therefore have current-past measurable L² variables at every time, without an adapted-solution premise. A standard strongly adapted representative is constructed with a.e. equality at each time; a separate theorem now constructs a simultaneous continuous original sampler version when the actual raw additive input has continuous paths.</p>',
        [('PBGSO/IntegralAdaptation.lean','integral_mem_subspace'),
         ('PBGSO/ConstructedAdaptation.lean','canonical_meanField_aestronglyAdapted'),
         ('PBGSO/ConstructedAdaptation.lean','particleRealization_aestronglyAdapted'),
         ('PBGSO/IntegralAdaptation.lean','adaptedRepresentative_stronglyAdapted')],
        sources, parsed, math, page, 'result-constructed-adaptation')
    body += result_panel('General state-dependent diffusion realized from martingale increments',
        r'<p>Actual continuous L² drift and diffusion columns realize the general model pointwise, retaining parameter- and state-dependent diffusion. The sampler drift residual has a standard martingale representative, the state is adapted, and SynchronousIsometry identifies the weighted residual-increment second moment with the actual diffusion-difference integral. The optimiser follows its original ODE.</p>'
        r'<p>These inputs derive the synchronous quadratic weak equation and, under source A3, its energy decay. No energy derivative or pair forward equation is assumed. Observation integrability and norm-continuous L² coefficient realizations are explicit; state second moments alone do not imply the required L² drift integrability for superlinear drifts. Marginal tests are empty and the pair domain the quadratic singleton; the actual computed integrator below now supplies martingale/isometry for arbitrary time-L² adapted columns. The original raw results above derive the appropriate calculus directly; this intermediate weak-generator interface alone does not assert a rich marginal Itô domain.</p>',
        [('PBGSO/GeneralMartingaleRealization.lean','ModelL2Trajectory'),
         ('PBGSO/GeneralMartingaleRealization.lean','SynchronousIsometry'),
         ('PBGSO/GeneralMartingaleRealization.lean','isCoupledWeakSolution_quadratic'),
         ('PBGSO/GeneralMartingaleRealization.lean','coupling_energy_decay')],
        sources, parsed, math, page, 'result-general-martingale')
    body += result_panel('Source A3 energy and transport decay with integrable coefficients',
        r'<p>The actual optimiser follows its original integral equation, the drift is Bochner L¹ in time with L² random-variable values, and each diffusion column is time-L². The actual sampler residual has a standard martingale representative. Exact quadratic increments derive the full expected energy balance; literal model coefficient identities and the actual joint-law pushforward transfer source A3 into dissipation.</p>'
        r'<p>This proves energy decay, actual joint-law RMS contraction and genuine marginal Wasserstein decay for the supplied initial coupling. Continuous coefficients and pointwise optimiser derivatives are unnecessary. The general interface retains actual stochastic weighted increment isometry; that property is independently constructed for arbitrary time-L² adapted finite columns. Extending the intended source A1 solution class to these integral/martingale contracts, including coefficient-moment/localization transfer, remains explicit. Simultaneous continuous versions in the displayed integrable class are now derived below. Source P₂ state moments alone do not establish all drift coefficient moments.</p>',
        [('PBGSO/IntegralModelContraction.lean','ModelIntegralTrajectory'),
         ('PBGSO/IntegralModelContraction.lean','pair_energy_integral'),
         ('PBGSO/IntegralModelContraction.lean','pair_energy_decay'),
         ('PBGSO/IntegralModelContraction.lean','pair_law_distance_decay')],
        sources, parsed, math, page, 'result-integrable-model')
    body += result_panel('Actual canonical state-dependent law contraction from computed Itô dynamics',
        r'<p>The model optimiser and sampler satisfy their original integral equations driven by the computed predictable Brownian integral. Drift is Bochner L¹ in time with L² random-variable values; diffusion has time-L² finite columns and current-past AE measurability. Literal coefficient identities retain the full parameter- and state-dependent diffusion. The probability/Borel complete-Hilbert setting, genuine finite-column Brownian Driver, actual observation integrability, original optimiser drift equation and measurable raw model drift are explicit.</p>'
        r'<p>The positive metric bounds and source A3 with \(\rho>0\) derive energy decay. Every genuine initial coupling receives the same two actual marginal trajectories on one full initial/noise filtration. Integral commutation, martingale/isometry, exact output laws and the Wasserstein infimum are proved internally, giving the source factor \(\sqrt\kappa e^{-\rho T}\) times the true initial optimiser–law distance.</p>'
        r'<p><strong>Remaining source bridge.</strong> The displayed Data contains original equations and integrability, with no final stochastic-energy or transport premise. It is an explicit actual realization class. The later raw linear-growth theorem now derives membership from original local strong equations in branch A1(ii). The superlinear constant-diffusion contraction branch A1(i) remains separate; actual path-space transfer proves frozen SDE stationarity on distinct sources.</p>',
        [('PBGSO/ConstructedPredictableModel.lean','Data'),
         ('PBGSO/ConstructedPredictableModel.lean','law_distance_decay'),
         ('PBGSO/ConstructedPredictableLaw.lean','law_distance_decay')],
        sources, parsed, math, page, 'result-constructed-model-law')
    body += result_panel('Exact particle interaction bound from computed time-L² Itô dynamics',
        r'<p>Actual full raw interacting/copy coefficients satisfy their original integral equation driven by the computed finite-column Brownian integral. The drift is time-L¹ with L² values and the packed diffusion merely adapted time-L². The actual raw drift and diffusion are measurable. The actual reference cloud alone has its iid population marginal; its optimiser is deterministic and its observation variance is uniformly bounded by \(V\). Source A3 and the gradient-response constant \(L_\Psi\) then prove</p>'
        r'<div class="equation">\[\bigl(\mathbb E[d_{\rm emp}(T)^2]\bigr)^{1/2}\le\frac{L_\Psi}{\rho}\sqrt{\frac{\kappa V}{N}}(1-e^{-\rho T}).\]</div>'
        r'<p>The energy balance, martingale, weighted stochastic isometry, exact Var/N forcing and empirical-statistic measurability are derived. No coefficient continuity, weak-test-domain, energy bound or stochastic-isometry conclusion is supplied. Positive N and rho, synchronous initial coordinates, the reference iid marginal, deterministic reference optimiser and variance are explicit. The final parameter triangle adds the actual mean-field optimiser distance to its target. General source A1 realization/localization remains separate.</p>',
        [('PBGSO/ConstructedPredictableParticle.lean','Data'),
         ('PBGSO/ConstructedPredictableParticle.lean','Data.finite_particle_interaction_bound'),
         ('PBGSO/ConstructedPredictableParticle.lean','Data.parameter_target_bound')],
        sources, parsed, math, page, 'result-constructed-particle')
    body += result_panel('One continuous original additive sampler version for every horizon time',
        r'<p>A Bochner L¹-time family of L² variables now has an actually constructed joint strongly measurable, product-integrable representative. Its literal pathwise primitive, together with the original raw additive input, yields one jointly strongly measurable sampler process with the same L² variable at every horizon time. Product Fubini transfers the original nonlinear drift equation on one spatial full-measure event for all times, and the paths are continuous there.</p>'
        r'<p>The direct mean-field theorem derives all drift realization and regularity from the actual global integral solution and primitive LipschitzDynamics. The remaining additional input is explicit: the raw additive input is jointly strongly measurable, represents the actual L² input at every horizon time, and has almost-sure continuous paths. The later actual Brownian-modification construction derives this condition from primitive Driver laws, and the final computed-model corollary discharges it internally. Combining the exact version identity with proved L² adaptation gives AE current-past measurability of the same version; strict adaptation under an uncompleted natural filtration is not asserted.</p>',
        [('PBGSO/LpJointRepresentative.lean','exists_joint_representative'),
         ('PBGSO/LpJointRepresentative.lean','jointRepresentative_setIntegral'),
         ('PBGSO/LpContinuousVersion.lean','exists_continuous_integral_version'),
         ('PBGSO/AdditiveContinuousVersion.lean','IsGlobalAdditiveIntegralSolution.exists_continuous_sampler_version')],
        sources, parsed, math, page, 'result-continuous-additive-version')
    body += result_panel('Constructed continuous Brownian drivers and original sampler paths',
        r'<p>Actual Gaussian fourth moments yield summable adjacent dyadic-grid tails. Borel–Cantelli and literal polygon interpolation derive continuous limits. An explicit strict-past series is adapted to the original filtration; countable-horizon overlap then constructs a globally continuous Brownian modification with the same random variable at every fixed time. Spatial increment independence and full future–past independence are preserved by proved almost-everywhere identities.</p>'
        r'<p>The original and modified Drivers have the exact same filtration, and the computed stochastic integral is proved invariant under this modification. Consequently every actual closed integral has a simultaneous continuous martingale version, and original model Data has one joint continuous sampler/noise realization satisfying its original nonlinear drift equation at every horizon time on a single probability-one event.</p>'
        r'<p><strong>No Brownian continuity premise remains in these final statements.</strong> The original model drift must be jointly strongly measurable on the chosen horizon; actual pathwise drift integrability is derived from its time-L¹(L²) contract. The selected joint sampler is proved AE adapted at every time; the constructed Brownian modification itself is strictly adapted to the original uncompleted filtration. Original raw Brownian representatives are not asserted to have continuous paths. Minimal source A1 localization remains separate.</p>',
        [('PBGSO/AdaptedBrownianModification.lean','exists_adapted_brownian_modification'),
         ('PBGSO/ContinuousBrownianDriver.lean','continuousDriver'),
         ('PBGSO/ConstructedContinuousIntegral.lean','exists_constructed_continuous_martingale_version'),
         ('PBGSO/ConstructedContinuousSampler.lean','Data.exists_continuous_sampler_version_constructed')],
        sources, parsed, math, page, 'result-constructed-continuous-paths')
    body += result_panel('Actual constant diffusion matching and independent-copy seeds',
        r'<p>Every finite family of constant diffusion columns determines a genuine continuous linear map from Euclidean noise. Its constructed normalized map exactly cancels the square-root-two scaling of the Brownian input constructor. The model column identity is proved for every constant-diffusion compatible model; no matrix-matching equality is assumed.</p>'
        r'<p>Separately, finite product sampling of complete one-copy seeds proves the actual fixed-time iid reference-cloud law and independence of whole coordinate trajectories. Those seeds may include the initial variable and its noise. Their L² coordinate pullbacks are genuine isometries. Identifying these variables with the intended reference equations and shared-driver particle/copy system remains a process obligation; no independence of interacting particles is inferred.</p>',
        [('PBGSO/AdditiveDiffusion.lean','additive_model_diffusion_columns'),
         ('PBGSO/AdditiveDiffusion.lean','samplerBrownianInput_normalized'),
         ('PBGSO/IndependentCopies.lean','cloud_law'),
         ('PBGSO/IndependentCopies.lean','trajectories_independent')],
        sources, parsed, math, page, 'result-diffusion-copies')
    body += result_panel('Energy decay and finite-particle comparison mechanism', PROSE['energy'],
        [('PBGSO/PaperTheorems.lean','forced_energy_bound'),('PBGSO/PaperTheorems.lean','distance_decay_of_energy'),
         ('PBGSO/PaperTheorems.lean','parameter_error_of_components')], sources, parsed, math, page, 'result-energy')
    body += result_panel('Actual empirical couplings and particle work',
        r'<p>Pairing particle i with reference particle i produces a genuine empirical coupling. Its quadratic cost is the average of the paired squared distances, so</p>'
        r'\[W_2^2(\nu^N,\bar\nu^{[N]})\le N^{-1}\sum_i\|Z_i-\bar Z_i\|^2.\]'
        r'<p>Positive N is explicit; no independence of the interacting cloud is assumed. The law-level joint condition is lifted to the actual finite averaged force and synchronous diffusion correction. The population-gradient discrepancy is exactly the empirical reference observation fluctuation. These facts do not identify the dynamically evolved reference cloud with an independent product law; that process-law obligation remains separate.</p>',
        [('PBGSO/EmpiricalMonotonicity.lean','particleCouplingWork_le'),
         ('PBGSO/EmpiricalMonotonicity.lean','particle_population_work_decomposition'),
         ('PBGSO/LawContraction.lean','empiricalCloud_wasserstein_sq_le'),
         ('PBGSO/ParticleWeakEnergy.lean','particleCopyGenerator_quadratic')],
        sources, parsed, math, page, 'result-empirical')
    body += result_panel('Empirical-cloud Wasserstein measurability is proved',
        r'<p>The actual empirical Wasserstein distance is measurable as a function of both finite clouds, including duplicate locations. Equality-pattern strata reduce its genuine coupling infimum to fixed finite index-coupling spaces; each transport cost is continuous in the clouds. This proves the empirical optimiser-plus-cloud metric is measurable and therefore AE strongly measurable under every actual joint law.</p>'
        r'<p>Positive particle count and Borel second-countable real Hilbert state coordinates are explicit. No optimal coupling, Wasserstein triangle inequality or desired-statistic measurability is assumed. This discharges the empirical-metric measurability contract in the general finite-particle bound under these standard structural conditions.</p>',
        [('PBGSO/EmpiricalMeasurability.lean','empirical_wasserstein_measurable'),
         ('PBGSO/EmpiricalMeasurability.lean','particleEmpiricalDistanceSq_aestronglyMeasurable')],
        sources, parsed, math, page, 'result-empirical-measurability')
    body += result_panel('Full finite-particle interaction bound from the actual generator',
        r'<p>The actual paired interacting/reference generator retains the complete state-dependent diffusion. Its quadratic forward equation, joint monotonicity, weighted Cauchy–Schwarz and the exact i.i.d.-cloud variance give</p>'
        r'\[\left(\mathbb E\left[\|s_t^N-\bar s_t\|^2+W_2^2(\nu_t^N,\bar\nu_t^{[N]})\right]\right)^{1/2}\le\frac{L_\Psi}{\rho}\sqrt{\frac{\kappa V}{N}}(1-e^{-\rho t}).\]'
        r'<p><strong>Exact additional premises.</strong> Positive N and rho; a particle/copy weak forward equation whose test domain contains the actual quadratic energy; zero initial coupling energy; an almost-surely deterministic reference optimiser; an actual reference-cloud marginal equal to the finite product of its common law; square-integrable observations; uniform centred variance V; optimiser response Lipschitz constant Lpsi; and the stated residual and empirical-metric AE measurability. EmpiricalMeasurability derives the actual Wasserstein statistic’s measurability for all joint laws in Borel second-countable Hilbert coordinates, discharging that metric contract. The forced-energy derivative and dissipation are derived, not assumed. Separate helper theorems derive residual AE measurability from the primitive response bound and actual iid reference marginal, and zero initial energy from synchronous initial coordinates. The interacting cloud need not be independent of itself or of the reference cloud. Translating source strong solutions and their dynamic independent copies into these generator and marginal contracts remains separate. The bound concerns interaction against the independent-copy empirical law; a population-law Wasserstein bound needs an additional empirical sampling term.</p>',
        [('PBGSO/ParticleWeakBound.lean','finite_particle_interaction_bound'),
         ('PBGSO/Sampling.lean','gradient_sampling_variance_of_cloud_law')],
        sources, parsed, math, page, 'result-particle-bound')
    body += result_panel('Constructed additive interacting/copy particle data',
        r'<p>Starting with an actual global one-copy integral reference, finite product seeds construct independent complete reference trajectories. The shared-optimiser interacting process is then constructed globally from the true finite empirical force and the same additive inputs. Its particle/copy quadratic generator equation, exact iid reference-cloud marginal, deterministic reference optimiser, observation square integrability, residual measurability and zero initial error are derived.</p>'
        r'<p>The final ParticleParameterApproximation is a constructed output. Positive particle count, primitive global Lipschitz maps, autonomous response and constant diffusion compatibility, continuous input starting at zero and the uniform observation-variance bound remain inputs. The generator domain is the particle quadratic singleton; this is an actual additive process theorem, without claiming a full marginal Itô equation or state-dependent strong-SDE realization.</p>',
        [('PBGSO/ParticleAdditiveWeakRealization.lean','exists_additive_particle_copy_weak'),
         ('PBGSO/ParticleAdditiveWeakRealization.lean','exists_additive_particle_approximation')],
        sources, parsed, math, page, 'result-additive-particle')
    body += result_panel('Actual random-parameter bound and joint large-time/large-particle limit',
        r'<p>The frozen target constant weak solution is constructed from its stationary generator, zero mean observation and optimiser fixed point. Full mean-field law contraction and the particle generator forcing are then combined with an internally proved L² triangle inequality and a one-Lipschitz parameter projection:</p>'
        r'\[\|P_\theta s_t^N-P_\theta s_\star\|_{L^2}\le\sqrt\kappa e^{-\rho t}d_0+\frac{L_\Psi}{\rho}\sqrt{\frac{\kappa V}{N}}(1-e^{-\rho t}).\]'
        r'<p>The proof establishes square integrability of the actual parameter error. It retains the explicit mean-field and particle/copy weak equations, quadratic generator domains, frozen stationary-target integrability, zero mean observation, optimiser fixed point at every nonnegative time, all-initial-coupling synchronous realization, actual iid reference cloud, uniform variance and the response/measurability/initial-energy contracts. No parameter-error, triangle or final rate premise is supplied. A uniform family satisfying these contracts has actual error tending to zero jointly as time and particle count tend to infinity; its positive count is indexed by n+1. This is a conditional weak-process theorem, with the strong-SDE realization bridge still explicit. The target is the source critical point; minimization needs its own assumption.</p>',
        [('PBGSO/ParameterBound.lean','finite_particle_parameter_bound'),
         ('PBGSO/ParameterBound.lean','finite_particle_parameter_joint_limit')],
        sources, parsed, math, page, 'result-parameter')
    body += result_panel('Separate primitive conditions in the actual coupling integral',
        r'<p>The primitive assumptions are same-law optimiser dissipation with rate rO, optimiser response Lipschitz constant Lpsi, sampler observation Lipschitz constant LF, frozen-sampler dissipation rS, parameter drift Lipschitz constant Lb and a full squared diffusion-column bound with constant Lsigma. Actual Bochner coupling identities, weighted Cauchy–Schwarz and integrated quadratic costs give the rate</p>'
        r'\[\rho_{\rm diag}=\min(r_O,r_S)-\tfrac12\kappa L_\sigma^2-\tfrac12\sqrt\kappa(L_\Psi L_F+L_b).\]'
        r'<p>This proves full law-level twisted joint monotonicity. Require the displayed rate to be positive for exponential contraction; this is exactly the source simpler diagonal condition. The full determinant criterion is proved below, including its equality with the actual minimum eigenvalue of the literal source matrix. No combined optimiser/sampler work estimate is assumed in place of the primitive conditions.</p>',
        [('PBGSO/SeparatedCriteria.lean','SeparatedAssumptions'),
         ('PBGSO/SeparatedCriteria.lean','separatedDiagonalRate'),
         ('PBGSO/SeparatedCriteria.lean','separated_joint_monotonicity_diagonal')],
        sources, parsed, math, page, 'result-separated')
    body += result_panel('Full source determinant small-gain criterion',
        r'<p>Let a=rO−kappa Lsigma²/2, b=rS−kappa Lsigma²/2 and c=sqrt(kappa)(Lpsi LF+Lb), so the off-diagonal entries of the source matrix are −c/2. Lean proves its quadratic-form lower bound at</p>'
        r'\[\rho_{\rm spec}=\frac{a+b-\sqrt{(a-b)^2+c^2}}2.\]'
        r'<p>The exact three source conditions 2rO−kappa Lsigma²>0, 2rS−kappa Lsigma²>0 and kappa(Lpsi LF+Lb)²<(2rO−kappa Lsigma²)(2rS−kappa Lsigma²) make this rate positive. The primitive separated assumptions imply actual full law-level twisted joint monotonicity at this explicit rate. The proof covers matrices that fail diagonal dominance and handles degenerate zero off-diagonal cases. A separate spectral proof identifies the closed-form rate with the actual minimum of the two matrix eigenvalues and proves the literal source matrix positive definite. The final theorem concludes actual full joint monotonicity at that minimum eigenvalue.</p>',
        [('PBGSO/SeparatedSchur.lean','separatedSpectralRate'),
         ('PBGSO/SeparatedSchur.lean','separatedSpectralRate_pos'),
         ('PBGSO/SeparatedSchur.lean','separated_joint_monotonicity_spectral'),
         ('PBGSO/SmallGainSpectrum.lean','separated_source_criterion')],
        sources, parsed, math, page, 'result-separated-spectral')
    body += result_panel('Projected sufficient conditions in the actual coupling integral',
        r'<p>Pointwise strong monotonicity of the projected score field, the two separate auxiliary dissipation inequalities, constant sampler diffusion, the stated linear projections and orthogonal norm splits imply actual twisted joint monotonicity. Coupling marginal identities and the projected score-work integrals are proved. Positive residual projected dissipation c and positive auxiliary coercivity constants give the certified rate</p>'
        r'\[\rho=\min\{c,m_{\rm lower},v_{\rm lower}\}/D_{\rm upper}>0.\]'
        r'<p>The score-work, projected position-square and auxiliary-square integrability contracts are explicit. This is a conservative certified rate; the exact generalized-eigenvalue rate in the source is not identified by this theorem.</p>',
        [('PBGSO/ProjectedCriteria.lean','projected_twistedJointMonotonicity_certified')],
        sources, parsed, math, page, 'result-projected')
    body += result_panel('Full canonical source projected-field criterion at its exact spectral rate',
        r'<p>In the source parameter/auxiliary and position/auxiliary Euclidean coordinates, assume the full metric matrices Dopt, Dsam and the two auxiliary matrices Dm, Dv are positive definite. U4 score monotonicity, the two separate U5 dissipations, constant diffusion, literal coordinate projections and positive c=beta r−Aopt−Asam construct</p>'
        r'\[\begin{gathered}K_{\rm opt}=\operatorname{diag}(cI,D_m),\\K_{\rm sam}=\operatorname{diag}(cI,D_v),\\A_j=D_j^{-1/2}K_jD_j^{-1/2},\\\rho=\min_j\lambda_{\min}(A_j)>0,\\j\in\{\mathrm{opt},\mathrm{sam}\}.\end{gathered}\]'
        r'<p>The actual full metric and its norm comparisons, SPD block K matrices, coordinate identities, inverse-square-root relation and exact minimum-eigenvalue quadratic bounds are derived. No representation or lower-comparison conclusion is assumed. Parameter and position dimensions are nonempty; auxiliary dimensions may be zero. The coupling score/position/auxiliary integrability domain is explicit. Separately, the ordinary finite reading of the universal U5 sampler integral is named FiniteSamplerDriftDomain. Its wrapper returns both the spectral joint inequality and FiniteCouplingWork for the constant-diffusion law theorem; a conditional inequality alone does not certify that domain.</p>',
        [('PBGSO/CanonicalProjectedCriterion.lean','canonical_projected_source_criterion'),
         ('PBGSO/ProjectedFiniteWork.lean','FiniteSamplerDriftDomain'),
         ('PBGSO/ProjectedFiniteWork.lean','canonical_projected_source_criterion_finite'),
         ('PBGSO/GeneralizedSpectrum.lean','generalizedMinimum_quadratic'),
         ('PBGSO/GeneralizedSpectrum.lean','whitened_eq_sqrt_inv')],
        sources, parsed, math, page, 'result-projected-canonical')
    body += result_panel('The source heavy-ball criterion with an explicit feasible metric and rate',
        r'<p>For the actual unit-mass heavy-ball optimiser and underdamped sampler, assume the joint projected force is r-strongly monotone and L-Lipschitz, r and gamma are positive, constant sampler diffusion, and the exact source threshold</p>'
        r'\[\gamma>\sqrt2 L/\sqrt r.\]'
        r'<p>Lean constructs the actual block weight with entries gamma I, I and 2 I/gamma, derives positive lower and finite upper comparisons, and chooses</p>'
        r'\[\eta=\frac{1+2L^2/(r\gamma^2)}2,\quad \varepsilon=1-\eta,\quad A=\frac{L^2}{\eta\gamma^2},\quad c=r-2A,\quad \rho=\frac{\min(c,\varepsilon)}{\gamma+1+2/\gamma}>0.\]'
        r'<p>The metric lower constant is min(gamma/4,1/(2 gamma)) and its upper constant is gamma+1+2/gamma. Separate auxiliary dissipation and all coupling score/position/auxiliary integrability estimates are proved from the primitive hypotheses. The conclusion is full twisted joint monotonicity of the actual constructed model and metric. The forces may be nonconservative and the optimiser and sampler position dimensions may differ. This source sufficient-condition proposition does not itself supply strong-SDE existence, stationarity or the variance assumption.</p>',
        [('PBGSO/HypocoerciveCriterion.lean','heavyBallModel'),
         ('PBGSO/HypocoerciveCriterion.lean','hypocoerciveGeometry'),
         ('PBGSO/HypocoerciveCriterion.lean','heavyBall_source_criterion')],
        sources, parsed, math, page, 'result-hypocoercive')
    body += result_panel('Both implementation drifts construct actual general models',
        r'<p>The M-MFPO model has complete Hilbert optimiser (theta,m) and sampler (x,v); the HOL model has optimiser theta and nested Hilbert sampler (x,u,v), with drift (u,−G+gamma v,−gamma u−alpha v) and noise only in the last sampler coordinate. The original F and G remain independent maps.</p>'
        r'<p>Separate primitive global Lipschitz bounds construct the full mean-field LipschitzDynamics, actual model compatibility and one-Lipschitz parameter projection. Both raw finite-empirical integral drifts intertwine exactly with those model drifts. No unrelated model equations or common potential are assumed. Source joint monotonicity, frozen invariance, variance and intended Brownian implementation remain their own hypotheses.</p>',
        [('PBGSO/ImplementationDynamics.lean','momentumDynamics'),
         ('PBGSO/ImplementationDynamics.lean','momentum_compatibility'),
         ('PBGSO/ImplementationDynamics.lean','higherOrderModel'),
         ('PBGSO/ImplementationDynamics.lean','higherOrder_compatibility'),
         ('PBGSO/ImplementationDynamics.lean','momentum_particle_drift'),
         ('PBGSO/ImplementationDynamics.lean','higherOrder_particle_drift')],
        sources, parsed, math, page, 'result-implementation-models')
    body += result_panel('Continuous and discrete frictionless volume preservation',
        r'<p>The discrete force kicks and position drifts preserve product Haar measure for arbitrary measurable forces. For a globally differentiable force in finite dimension, their actual shear derivatives and the chain rule also prove signed determinant one for the original B-A-B implementation. For an arbitrary C¹ position force and actual globally defined frictionless ODE trajectories, the continuous proof derives joint C¹ flow dependence, its variational equation and determinant derivative, then proves</p>'
        r'\[\det D\Phi_t(x)=1.\]'
        r'<p><strong>The source flow assumptions suffice.</strong> Supply only the C¹ force, actual ODE at every time and state, and identity initial map. Joint continuity and differentiability of the flow, a variational equation, globally Lipschitz cutoff fields and determinant preservation are derived. The proof constructs genuine globally Lipschitz cutoff trajectories, proves local equality near each compact orbit and transfers the path-space Picard/implicit-function regularity. ODE uniqueness also derives the group identity and negative-time inverse. Jacobian change of variables then proves literal Lebesgue MeasurePreserving for every real-time slice, with no injectivity or inverse premise. The joint force may be nonconservative. Friction and stochastic thermostat steps are outside these claims.</p>',
        [('PBGSO/ContinuousFlowMeasure.lean','phase_flow_measurePreserving_source'),
         ('PBGSO/FlowSourceRegularity.lean','phase_flow_fderiv_det_one_source'),
         ('PBGSO/FlowSourceRegularity.lean','flow_contDiff'),
         ('PBGSO/ContinuousVolume.lean','phase_flow_fderiv_det_one_C1'),
         ('PBGSO/FlowDifferentiability.lean','flow_contDiff_of_globalLip'),
         ('PBGSO/FlowDifferentiability.lean','phase_flow_fderiv_det_one_globalLip'),
         ('PBGSO/FlowLocalization.lean','exists_global_lipschitz_C1_cutoff'),
         ('PBGSO/DiscreteVolume.lean','interwovenBAB_fderiv_det_one'),
         ('PBGSO/Volume.lean','interwovenBAB_preserves')],
        sources, parsed, math, page, 'result-volume')
    body += result_panel('Exact source parameter bound for constructed additive processes',
        r'<p>The canonical one-copy trajectory, its independent complete reference cloud and the actual interacting trajectory are constructed from the primitive globally Lipschitz maps. The actual frozen invariant sampler constructs the stationary target and every target coupling. The exact shared parameter-law identity is proved internally. The resulting actual random parameter obeys the displayed source relaxation-plus-particle bound.</p>'
        r'<p>The final theorem assumes no weak-process package, iid-cloud identity, residual measurability, zero initial energy, target realizer or compatible output-law conclusion. Its inputs are the autonomous additive maps and model compatibility, actual frozen invariant trajectory, positive source A3, one-Lipschitz parameter projection, positive N and uniform observation variance. ImplementationDynamics derives compatibility for the concrete methods from their primitive F/G force bounds. The theorem concerns the constructed continuous additive processes; the general state-dependent raw-SDE results are stated above.</p>',
        [('PBGSO/ConstructedParameterBound.lean','parameter_bound')],
        sources, parsed, math, page, 'result-constructed-parameter')
    body += result_panel('New A and New B: time-uniform actual implementation bounds',
        r'<p>Both actual particle methods now satisfy a discretisation error bound D sqrt(h) for every iteration, under an explicit positive threshold h_max. Source A3 constructs the contracting metric on the literal raw implementation coordinates. Exact Picard restarts, uniform continuous-reference moments and actual Gaussian local errors are proved before small-step absorption is applied.</p>'
        r'\[\begin{gathered}D=\frac{4(a+bR)}{\rho m_C},\\ h_{\max}=\min\{1,\rho^{-1},[\rho/(4(b+1))]^2\}.\end{gathered}\]'
        r'<p>The final target theorem adds this time-uniform discretisation term to the source continuous relaxation and particle floor. Independent globally jointly Lipschitz forces, finite-dimensional optimiser/sampler coordinates, the physical parameter signs, P2 initial/target laws, actual frozen invariance, zero mean target observation, source A3 and A5 remain explicit. There is no supplied numerical contraction, local defect, uniform moment estimate or error recurrence. The constants may depend on fixed N. The original finite-horizon results below remain supporting theorems. See the main page for exactly the two final theorem statements and the standalone verification commands.</p>',
        [('PBGSO/FullyUniformMomentum.lean','numerical_parameter_bound'),
         ('PBGSO/FullyUniformHigherOrder.lean','parameter_bound'),
         ('PBGSO/ImplementationMetric.lean','momentum_metric'),
         ('PBGSO/ImplementationMetric.lean','higherOrder_metric'),
         ('PBGSO/UniformIntegralMoments.lean','uniform_moment'),
         ('PBGSO/UniformDiscrete.lean','one_step_same_initial_uniform_norm'),
         ('PBGSO/UniformStepSize.lean','admissible')],
        sources, parsed, math, page, 'result-time-uniform-numerics')
    body += result_panel('M-MFPO: earlier finite-horizon additive implementation-to-target bound',
        r'<p>The actual heavy-ball optimiser, underdamped sampler and finite interacting particle process are constructed from the original independent forces. Genuine same-sample L² coordinates identify the full original integral dynamics. The two normalized half-grid Gaussian innovations are exactly coupled to that process Brownian input. Compactness and actual Brownian increments derive mesh-independent constants P,G,R on each fixed finite horizon.</p>'
        r'<p>Write \(E_n=\|\widehat\theta_n^{N,h}-\theta_\star\|_{L^2}\). Then</p>\[\begin{aligned}E_n&\le B_M(h,n;0)\\ &+\sqrt\kappa e^{-\rho nh}d_0\\ &+c_M(1-e^{-\rho nh}),\\ c_M&=\frac{2+\gamma}{\rho}\sqrt{\frac{\kappa V}{N}},\\ &\quad 0<h\le1,\ nh\le T.\end{aligned}\]'
        r'<p>The explicit earlier square-root-step budget uses the derived momentum radius P, force radius G+gamma P and increment modulus R, with zero initial discretization error. The response constant 2+gamma is the constructed bound for this complete heavy-ball optimiser in its Hilbert coordinates. The final theorem assumes no reference, moment/modulus estimate, weak-process package or compatible law identity.</p>'
        r'<p><strong>Remaining inputs.</strong> Complete Borel second-countable Hilbert optimiser coordinates, separate global joint Lipschitz bounds for F and G, positive particle count and literal flattened Euclidean encoding, gamma≥0, P₂ initial and target laws, the actual frozen invariant sampler, zero target mean observation, positive source A3 metric/rate, and uniform observation variance along the actual canonical mean-field path. The target optimiser has zero momentum; its fixed-point identity is proved. These sufficient Lipschitz hypotheses are not asserted for arbitrary nonsmooth or neural EBM examples. These are constructed autonomous additive integral dynamics and a fixed-horizon numerical guarantee.</p>',
        [('PBGSO/FullyConstructedMomentum.lean','numerical_parameter_bound'),
         ('PBGSO/MomentumIntegralConstruction.lean','exists_momentum_references_from_source')],
        sources, parsed, math, page, 'result-fully-constructed-momentum')
    body += result_panel('HOL-MYPGD: earlier finite-horizon additive implementation-to-target bound',
        r'<p>Starting with the original independent force maps, the actual physical HOL model and global interacting particle process are constructed. Explicit continuous linear coordinates prove its original shared L² implementation equations and parameter identity. The original Brownian input is exactly the pulled fourth Gaussian kernel; the full implementation innovation array has the proved manuscript covariance and independence. Compactness and actual Brownian increments derive all force, auxiliary and drift-modulus constants once per finite horizon, uniformly over its meshes.</p>'
        r'<p>Write \(E_n=\|\widehat\theta_n^{N,h}-\theta_\star\|_{L^2}\). Then</p>\[\begin{aligned}E_n&\le B_H(h,n;0)\\ &+\sqrt\kappa e^{-\rho nh}d_0\\ &+\frac1\rho\sqrt{\frac{\kappa V}{N}}(1-e^{-\rho nh}),\\ &\qquad 0<h\le1,\ nh\le T.\end{aligned}\]'
        r'<p>Here \(B_H\) is the previously proved explicit square-root-step budget, with zero initial discretization error, \(F_\theta=G\), \(F_G=G+\gamma P+L_GG\) and \(U=V=P\). The final theorem derives nonnegative P,G,C independently of the mesh. It assumes no integral reference, moment/modulus estimate, final law identity or weak-process package.</p>'
        r'<p><strong>Remaining inputs.</strong> Complete Borel second-countable Hilbert coordinates; separate global joint Lipschitz bounds for F and G; positive particle count and the literal flattened Euclidean encoding; alpha&gt;0 and gamma≥0; P₂ initial and target laws; the actual frozen invariant sampler trajectory driven by the physical input; zero target mean observation; a positive source A3 rate and metric; and uniform observation variance along the actual canonical mean-field path. The target is that stationary critical point. These sufficient Lipschitz hypotheses are not asserted for arbitrary nonsmooth or neural EBM examples. These are additive autonomous integral dynamics. A general multiplicative strong-SDE interpretation and uniform-in-time numerical mixing are not claimed.</p>'
        r'<p>The original-target corollary adds L epsilon/m only from an actual coupled original/surrogate pair, expectation identities and the positive-m gradient pairing. The coupling radius remains a visible model assumption. The printed full-space TV prior is improper; repairing that illustrative example is not an additional generic-method proof obligation.</p>',
        [('PBGSO/FullyConstructedHigherOrder.lean','parameter_bound'),
         ('PBGSO/FullyConstructedHigherOrder.lean','original_parameter_bound'),
         ('PBGSO/HigherOrderIntegralReference.lean','exists_higherOrderReference_of_particle_integral')],
        sources, parsed, math, page, 'result-fully-constructed-hol')
    body += result_panel('M-MFPO: new verified map bounds', PROSE['momentum'],
        [('PBGSO/Methods.lean','obabo_error'),('PBGSO/Methods.lean','obabo_finite_error')],
        sources, parsed, math, page, 'result-momentum')
    body += result_panel('M-MFPO: finite-horizon integral-reference error', PROSE['momentum-consistency'],
        [('PBGSO/MomentumConsistency.lean','momentumRemainderBudget'),
         ('PBGSO/MomentumConsistency.lean','obabo_integral_reference_finite_bound')],
        sources, parsed, math, page, 'result-momentum-consistency')
    body += result_panel('M-MFPO: explicit square-root-step rate', PROSE['momentum-rate'],
        [('PBGSO/MomentumRates.lean','momentumStabilityConstant'),
         ('PBGSO/MomentumRates.lean','momentumLocalConsistencyConstant'),
         ('PBGSO/ParticleMethodLp.lean','m_mfpo_particle_lp_gaussian_finite_bound'),
         ('PBGSO/ParticleMethodLp.lean','obaboStep_Lp_coe'),
         ('PBGSO/MomentumBrownian.lean','momentumHalfNoise_pathLaw'),
         ('PBGSO/MomentumBrownian.lean','momentumBrownian_noise_bound')],
        sources, parsed, math, page, 'result-momentum-rate')
    body += result_panel('HOL-MYPGD: new verified quadrature bound', PROSE['higher-order'],
        [('PBGSO/HigherOrderMethod.lean','endpoint_quadrature_error'),
         ('PBGSO/HigherOrderMethod.lean','higherOrder_quadrature_error')],
        sources, parsed, math, page, 'result-higher-order')
    body += result_panel('HOL-MYPGD: finite-horizon integral-reference error', PROSE['higher-order-consistency'],
        [('PBGSO/HigherOrderMethod.lean','holAmplification'),
         ('PBGSO/HigherOrderConsistency.lean','holDeterministicBudget'),
         ('PBGSO/HigherOrderConsistency.lean','higherOrder_integral_reference_finite_bound')],
        sources, parsed, math, page, 'result-higher-order-consistency')
    body += result_panel('HOL-MYPGD: explicit square-root-step rate and constructed Gaussian coupling', PROSE['higher-order-rate'],
        [('PBGSO/HigherOrderRates.lean','holStabilityConstant'),
         ('PBGSO/HigherOrderRates.lean','holLocalConsistencyConstant'),
         ('PBGSO/ParticleMethodLp.lean','hol_mypgd_particle_lp_gaussian_finite_bound'),
         ('PBGSO/ParticleMethodLp.lean','higherOrderStep_Lp_coe'),
         ('PBGSO/HOLNoise.lean','holScalarNoise_jointLaw'),
         ('PBGSO/HOLNoiseRates.lean','holVectorNoise_error_le'),
         ('PBGSO/HOLCovariance.lean','holCovarianceMatrix_eq_gram'),
         ('PBGSO/HOLCovariance.lean','holTripleNoise_jointLaw')],
        sources, parsed, math, page, 'result-higher-order-rate')
    body += result_panel('HOL Gaussian bounds on actual independent initial/noise particle spaces',
        r'<p>Each actual particle seed pairs an initial sampler variable with an independent canonical Brownian source. Forgetting the initial states and flattening particle/spatial indices preserves the entire canonical noise source. The initial cloud has the exact iid marginal and is independent of that whole Brownian source, proved through their actual joint product law. The actual four-kernel HOL innovation array, including the coupled Brownian reference coordinate, therefore retains its full temporal/spatial joint law.</p>'
        r'<p>Isometric L² pullback preserves the explicit Gaussian coupling budget and the actual finite-horizon particle bound on this random-initial space. The generic pullback theorem displays its measure-preserving projection; ParticleNoiseSpace constructs that projection rather than assuming a final noise-law identity. Original integral-reference segments, coefficient signs, finite-horizon forces/velocities and square-root modulus remain explicit.</p>',
        [('PBGSO/ParticleNoiseSpace.lean','noise_preserving'),
         ('PBGSO/ParticleNoiseSpace.lean','initial_noise_preserving'),
         ('PBGSO/ParticleNoiseSpace.lean','initial_noise_independent'),
         ('PBGSO/HOLPullback.lean','holPullbackVectorNoise_array_law'),
         ('PBGSO/HOLPullback.lean','HigherOrderPullbackIntegralReference.finite_bound')],
        sources, parsed, math, page, 'result-hol-pullback')
    body += result_panel('Parameter-law compatibility proved for actual shared numerical packing',
        r'<p>The full momentum state is packed into a shared Hilbert optimiser (theta,m) and per-particle Hilbert sampler (x,v); HOL uses optimiser theta and nested Hilbert sampler (x,u,v). The full packed variables are square integrable, their pointwise identities are proved, and their actual paired-law parameter marginal equals the original phase theta law.</p>'
        r'<p>These are actual pushforward identities, with no final compatibility equality premise and no independence of interacting particles. The generic theorem also covers the actual parameter lift of a constructed L² interacting optimiser. Thus the numerical target-law premise is discharged when the same actual reference process and packing are used; identifying independently supplied numerical integral references with a different process construction remains a separate equation-level task.</p>',
        [('PBGSO/ParameterLawTransfer.lean','optimizer_parameter_law'),
         ('PBGSO/ParameterLawTransfer.lean','momentum_hilbert_lp_parameter_law'),
         ('PBGSO/ParameterLawTransfer.lean','higherOrder_hilbert_lp_parameter_law')],
        sources, parsed, math, page, 'result-parameter-law-transfer')
    body += result_panel('Actual numerical parameter bounds to stationary and original targets',
        r'<p>The actual particle method parameter errors now combine the explicitly proved Gaussian discretization budgets with the actual weak-process stationary parameter bound:</p>'
        r'\[\|\widehat\theta_{n}^{N,h}-\theta_\star\|_{L^2}\le B_{\rm disc}(h,n)+\sqrt\kappa e^{-\rho nh}d_0+\frac{L_\Psi}{\rho}\sqrt{\frac{\kappa V}{N}}(1-e^{-\rho nh}).\]'
        r'<p>The budget Bdisc is exactly the earlier M-MFPO or HOL finite-horizon square-root-step expression, including its initial error. The integral-reference packages contain the primitive force, Brownian, compatible integral-equation, finite-horizon moment and modulus contracts; the stationary-target package contains the weak-generator, frozen-target and all-initial-coupling realization data. Neither package contains the requested final error bound as a field.</p>'
        r'<p><strong>Generic weak-process interface.</strong> Reference-law compatibility remains explicit in these intermediate statements. The numerical reference parameter law at time nh must equal the interacting optimiser parameter law used in the weak-process theorem. A proved pushforward identity and L² triangle transfer the reference bound; the code does not infer this law equality merely from the two separate solution descriptions.</p>'
        r'<p>For HOL, changing from its surrogate stationary target to the original zero-gradient target adds the proved bias L epsilon/m. Its assumptions are an actual L² pair of original/surrogate target sampler variables within epsilon, the original gradient expectation identity, zero surrogate mean observation, a spatial L-Lipschitz observation, and the displayed positive-m gradient monotonicity pairing. The Moreau-specific epsilon and proper TV-prior repair are not proved. These are finite-horizon conditional bounds; they do not assert uniform-in-time numerical mixing.</p>',
        [('PBGSO/NumericsTarget.lean','m_mfpo_numerical_parameter_bound'),
         ('PBGSO/NumericsTarget.lean','hol_mypgd_numerical_parameter_bound'),
         ('PBGSO/NumericsTarget.lean','hol_mypgd_original_parameter_bound')],
        sources, parsed, math, page, 'result-numerical-target')
    body += result_panel('Checked correction: the HOL coefficients are not the full exact linear flow',
        PROSE['coefficient-audit'],
        [('PBGSO/HOLCoefficientAudit.lean','hol_linear_coefficient_defect'),
         ('PBGSO/HOLCoefficientAudit.lean','hol_linear_coefficient_not_exact')],
        sources, parsed, math, page, 'result-coefficient-audit')
    body += result_panel('Hybrid-target bias from a supplied original/surrogate coupling',
        '<p>If the original gradient is strongly monotone with positive constant m, its target star has zero gradient, the surrogate mean original observation vanishes at a, and an actual original/surrogate sampler coupling at a has L² radius epsilon, a spatial L-Lipschitz observation gives distance at most L epsilon/m. The proof compares the actual Bochner force expectations and applies the gradient residual bound. This does not assume or prove a Moreau coupling radius for the TV example.</p>',
        [('PBGSO/TargetBias.lean','hybrid_target_bias')], sources, parsed, math, page, 'result-target-bias')
    body += '</section><section class="section" id="limitations"><h2>Model and target conditions</h2>' + math(PROSE['model-limitations']) + '</section>'
    audit = json.loads((ROOT/'PBGSO/exposition/reference_audit.json').read_text())
    roles = {
        'thm:invariant_measure': 'Weak-generator and actual integral-equation stationarity with literal product-law equality proved; intended Itô/process-class instantiation remains conditional.',
        'thm:twisted_joint_strong_monotonicity': 'Full multiplicative weak-generator energy and optimal Wasserstein product-distance contraction proved. Actual global additive law trajectories and all-initial-couplings quadratic realization are constructed. Full strong-SDE equivalence and state-dependent realization remain.',
        'thm:finite_particle_error': 'Full empirical interaction RMS bound derived from the actual multiplicative particle/copy weak generator and iid reference marginal. Strong-SDE/domain and evolved-copy-law realization remain.',
        'thm:parameter_error_full': 'Actual random-parameter L² bound and joint large-time/large-particle limit proved from the weak-generator process contracts and constructed frozen target. Source strong-SDE/domain and copy-law realization remain.',
        'cor:separate_monotonicity': 'The three exact source conditions prove positive-definite H and actual law-level joint monotonicity at the actual minimum eigenvalue; its closed form and simpler diagonal branch are also proved.',
        'cor:projected_strong_convexity': 'Primitive SPD block matrices, U4/U5 and constant diffusion construct the actual metric and exact generalized minimum-eigenvalue rate. The finite coupling-integrability domain is explicit.',
        'unlabeled:mpgd_hypocoercivity': 'Actual metric construction and full law-level joint monotonicity from original joint monotonicity/Lipschitz hypotheses and exact friction threshold, with explicit positive rate.',
        'lemma:vol_preserve_ode': 'Source continuous and discrete signed determinant-one statements verified. Joint C¹ flow regularity is derived from the primitive C¹ force and actual globally defined ODE; discrete Haar preservation also holds for merely measurable forces.',
    }
    body += '<section class="section" id="source-inventory"><h2>Every numbered source result</h2><div class="table-wrap"><table><thead><tr><th>Source result</th><th>Label</th><th>Formal coverage and remaining bridge</th></tr></thead><tbody>'
    for result in audit['results']:
        coverage = audit['formal_coverage'][result['id']]
        links = ' · '.join(f'<a href="{relative(proof_page(item["file"]),page)}#{anchor(item["name"])}"><code>{E(item["name"])}</code></a>' for item in coverage['declarations'])
        remaining = ''.join('<li>'+E(item)+'</li>' for item in coverage['remaining_obligations'])
        body += '<tr><td>' + E(result['kind'].title()+' '+result['number']) + '</td><td><code>' + E(result['label'] or 'unlabelled; app:mpgd_result') + '</code></td><td><strong>' + E(coverage.get('display_status', coverage['status'].title())) + '.</strong> ' + E(coverage.get('scope_note', roles[result['id']])) + '<p>'+links+'</p>'
        if remaining:
            body += '<details><summary>Remaining proof obligations</summary><ul>'+remaining+'</ul></details>'
        body += '</td></tr>'
    body += '</tbody></table></div><p>The source has eight numbered results and ten assumptions. <a href="source_audit.md">Detailed source and model audit</a> · <a href="reference_audit.json">Machine-readable result and assumption inventory</a>. The appendix gives proofs for the four main theorems rather than four additional numbered statements.</p>'
    body += '<h3>New actual method bounds</h3><div class="table-wrap"><table><thead><tr><th>Method</th><th>Verification and exact scope</th></tr></thead><tbody>'
    for name, coverage in audit['additional_method_coverage'].items():
        links = ' · '.join(f'<a href="{relative(proof_page(item["file"]),page)}#{anchor(item["name"])}"><code>{E(item["name"])}</code></a>' for item in coverage['declarations'])
        body += '<tr><td>'+E(name)+'</td><td><strong>'+E(coverage['status'].title())+'.</strong> '+E(coverage['scope_note'])+'<p>'+links+'</p></td></tr>'
    body += '</tbody></table></div>'
    incomplete = any(c['status'] != 'verified' for c in audit['formal_coverage'].values()) or any(c['status'] != 'verified' for c in audit['additional_method_coverage'].values()) or bool(audit.get('open_formal_obligations'))
    if incomplete:
        body += '<p>The strict coverage command currently rejects the remaining obligations shown in the ledger.</p>'
    else:
        body += '<p>The strict coverage command verifies all eight source results and both method bounds under the explicit source interpretations above, including the finite signed-work convention for the constant-diffusion source2 branch.</p>'
    body += '</section>'
    body += '<section class="section" id="modules"><h2>Supporting proofs and assumption notes</h2><div class="module-grid">'
    for path in sources:
        title, summary, scope = module_note(path)
        body += f'<article class="module-card"><a href="{relative(proof_page(path),page)}">{E(title)}</a><code>{E(path)}</code><p>{E(summary)}</p><p><strong>Assumptions and limits.</strong> {E(scope)}</p></article>'
    body += '</div></section><section class="section" id="verification"><h2>Compile and verify</h2>'
    body += '<pre class="commands"><code>lake build PBGSO\nlake env lean PBGSO/Check.lean\npython3 -B docs/build_site.py\npython3 -B scripts/verify-pbgso.py\npython3 -B scripts/verify-pbgso.py --require-complete</code></pre>'
    body += '<p>Lean checks the formal proofs. The default PBGSO verifier checks source hashes, every displayed declaration, exact assumption inventory, source-result coverage, local links and regeneration. Its successful run certifies documentation fidelity, not completion of all paper theorems. The strict <code>--require-complete</code> command rejects any open source-result, actual method-bound or required bridge obligation. Its source correspondence uses the documented SDE meaning of A2 and ordinary finite signed-work convention for the constant-diffusion source2 branch; an extended-negative-work theorem is not claimed. The audit file exposes logical axioms separately from analytic theorem premises. This source-based development has no proof PDF export.</p></section>'
    from report_citations import citation_panel
    body += citation_panel(None, None, None, page)
    return shell(page, 'PBGSO proof details and complete catalog', body, 'PBGSO')


def module_document(path, sources, parsed):
    page = proof_page(path)
    title, summary, scope = module_note(path)
    body = (f'<div class="breadcrumb"><a href="{relative(OVERVIEW,page)}">PBGSO overview</a> / {E(path)}</div>'
            f'<header class="hero module-hero"><div class="eyebrow">Exact declarations · explicit assumptions</div><h1>{E(title)}</h1>'
            f'<p>{E(summary)}</p><p class="correspondence-note"><strong>Assumptions and formal scope.</strong> {E(scope)}</p>'
            f'<p><a href="{relative(path,page)}">Lean source</a> · <a href="{relative("PBGSO/exposition/assumption_inventory.json",page)}">Exact assumption inventory</a></p></header>' + toolbar())
    body += '<section class="section" id="declarations"><h2>Definitions and complete proofs</h2><p>Each box reproduces the complete current declaration. Shared typeclasses, variables and namespace context are in the complete module below. Analytic premises in these signatures are assumptions of that theorem.</p>'
    for name, decl in parsed[path].items():
        description = source_docstring(sources[path], decl['start'])
        body += f'<article class="proof-step" id="{anchor(name)}"><h3>{E(name)}</h3><div class="pair"><div class="math-pane"><div class="pane-label">Mathematical role and assumptions</div>'
        body += '<p>' + E(description or 'Supporting declaration. The exact signature and complete source specify its quantified inputs and conclusion.') + '</p>'
        body += '<p>Read this statement with the module assumption note above. The complete proof appears alongside it; the full source preserves every shared variable and typeclass.</p></div><div class="lean-pane">'
        body += code(path, decl['start'], decl['end'], sources, page, 'declaration', name)
        body += '</div></div></article>'
    body += '</section><details class="source-section" id="complete-source"><summary>Complete Lean source, imports and shared assumptions</summary>'
    body += code(path,1,len(sources[path].splitlines()),sources,page,'module') + '</details>'
    from report_citations import citation_panel
    body += citation_panel(None, None, None, page)
    return shell(page, title, body, 'PBGSO')


def outputs():
    from pbgso_overview import overview_document
    sources, parsed = source_inventory()
    math_inputs = []
    def collect_math(text):
        math_inputs.append(text)
        return text
    # Collect the exact overview prose, including the inline theorem panels.
    overview_document(sources, parsed, collect_math)
    technical_document(sources, parsed, collect_math)
    math = HELPERS.render_mathematics(math_inputs)
    result = {OVERVIEW: overview_document(sources, parsed, math),
              CATALOG: technical_document(sources, parsed, math)}
    result.update({proof_page(path): module_document(path, sources, parsed) for path in sources})
    result['PBGSO/exposition/assumption_inventory.json'] = json.dumps(
        assumption_inventory(sources, parsed), indent=2, ensure_ascii=False) + '\n'
    return result


def authoring_inputs():
    sources, _ = source_inventory()
    return ['docs/build_pbgso.py', 'docs/pbgso_overview.py', 'docs/assets/pbgso.css',
            'scripts/check-pbgso-standalone.py',
            'docs/test_pbgso_landing.py', 'docs/test_pbgso_headers.py',
            'scripts/verify-pbgso.py', 'PBGSO/README.md',
            'PBGSO/exposition/source_audit.md', 'PBGSO/exposition/reference_audit.json'] + list(sources) + sorted(
                p.relative_to(ROOT).as_posix() for p in (ROOT/'standalone/PBGSO').glob('*.lean'))


if __name__ == '__main__':
    for path, text in outputs().items():
        target = ROOT/path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)
    print('Built PBGSO overview, complete declaration pages and exact assumption inventory.')
