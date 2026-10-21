<section class="main-theorem" id="main-theorem" aria-labelledby="main-theorem-title">
<h2 id="main-theorem-title">Main theorem. Gaussian ULA for a strongly convex potential</h2>
<p class="theorem-plain"><strong>What we prove:</strong> a bound on the quadratic Wasserstein distance from the actual ULA output to Gibbs measure. The only assumptions on the potential are differentiability, strong convexity, and a Lipschitz gradient. The reference process and its required moments are constructed in the supporting modules.</p>

<p>The complete assembly is <a href="#module-unadjustedlangevin-canonicalula-lean"><code>CanonicalULA.lean</code></a>. The analytic coupling argument has one implementation in <code>ULA.Hilbert</code>; IPLA applies it to the lifted particle potential. <code>L2Convergence.lean</code> preserves the earlier Euclidean API through specialization.</p>
<h3>The algorithm and its assumptions</h3>
<p>Let \(d\ge1\), and let \(U:\mathbb R^d\to\mathbb R\) be differentiable and \(m\)-strongly convex, with \(L\)-Lipschitz gradient, where \(0<m\le L\). Its Gibbs probability measure is</p>
\[\pi(dx)=Z^{-1}e^{-U(x)}dx,\qquad Z=\int_{\mathbb R^d}e^{-U(x)}dx\in(0,\infty).\]
<p>Let \(X_0\) have law \(\mu\), with finite second moment. Let the innovations \(\xi_k\) be independent standard Gaussian vectors, independent of \(X_0\). For a step \(h>0\), define</p>
\[X_{k+1}=X_k-h\nabla U(X_k)+\sqrt{2h}\,\xi_k.\]
<p>Equivalently, its laws are \(\mu_n=\operatorname{ulaLawStep}(U,h)^{[n]}\mu\). The recursion on measures is identified with the Gaussian random-variable algorithm by a proved law-equality theorem. Set</p>
\[C_0=W_2(\mu,\pi).\]
<p>Gibbs normalization and its second moment follow from the potential assumptions. The abstract initial-law endpoint displays \(C_0<\infty\); for an L² initial random vector this is derived from its finite second moment.</p>

<h3>Conclusion, for every iteration count \(n\in\mathbb N\)</h3>
<p><strong>Small-step case:</strong> if \(0<h\le 2/(m+L)\), then</p>
\[\boxed{W_2\bigl(\operatorname{Law}(X_n),\pi\bigr)
 \le (1-mh)^n W_2(\mu,\pi)+1.65\,\frac{L}{m}\sqrt{hd}.}\]
<p class="theorem-proof-link"><a href="#decl-unadjustedlangevin-hilbertdalalyan-dalalyan_small_step_of_integral_reference">Read the shared proof and its Lean notes</a> · final endpoint <code>ULA.Hilbert.dalalyan</code></p>
<p><strong>Large-step case:</strong> if \(2/(m+L)\le h<2/L\), then</p>
\[\boxed{W_2\bigl(\operatorname{Law}(X_n),\pi\bigr)
 \le (Lh-1)^n W_2(\mu,\pi)+1.65\,\frac{Lh}{2-Lh}\sqrt{hd}.}\]
<p class="theorem-proof-link"><a href="#decl-unadjustedlangevin-hilbertdalalyan-dalalyan_large_step_of_integral_reference">Read the shared proof and its Lean notes</a> · final endpoint <code>ULA.Hilbert.dalalyan_large_step</code></p>
<p>The coefficient \(1.65\) is the exact rational number \(33/20\). The upper bound \(h<2/L\) in the large-step case is strict. The two formulas agree at \(h=2/(m+L)\).</p>

<h3>How to read the conclusion</h3>
<p><strong>The left side compares distributions.</strong> \(\operatorname{Law}(X_n)\) is the output distribution. \(W_2\) is the infimum of root mean square separations over all couplings of the two laws. The initial term uses that infimum, with no assumption that an optimal coupling exists.</p>
<p><strong>The first term remembers the starting law.</strong> In each permitted regime its factor \(q\), equal to \(1-mh\) or \(Lh-1\), satisfies \(0\le q<1\). Thus \(q^n C_0\) tends to zero with the iteration count.</p>
<p><strong>The second term bounds discretization error.</strong> It is independent of \(n\), and decreases as \(\sqrt h\) in the small-step regime. The estimate does not claim exact sampling from Gibbs measure for a fixed positive step.</p>

<details class="reference-assumptions" id="main-reference-assumptions">
<summary>The constructed reference: which facts does the shared proof use?</summary>
<p>The analytic stage uses continuous curves \(Y_{k,t}\) in \(L^2(P;\mathbb R^d)\), with noise increments \(B_{k,t}\). For \(0\le t\le h\), they satisfy</p>
\[Y_{k,t}-Y_{k,0}=-\int_0^t\nabla U(Y_{k,s})\,ds+B_{k,t},\]
\[\|\nabla U(Y_{k,t})\|_2\le\sqrt{Ld},\qquad
  \|B_{k,t}\|_2\le\sqrt{2d}\sqrt t.\]
<p>The segments join, their endpoint noise agrees with the algorithm, and their laws are stationary:</p>
\[Y_{k,h}=Y_{k+1,0},\qquad B_{k,h}=\sqrt{2h}\,\xi_k,
 \qquad\operatorname{Law}(Y_{k,0})=\pi.\]
<p>These are L² identities and moment bounds. They appear as fields of <a href="#decl-unadjustedlangevin-hilbertdalalyan-L2Reference"><code>ULA.Hilbert.L2Reference</code></a> so the analytic calculation can be reused. The canonical endpoint constructs all these fields. Gibbs stationarity follows from exactly invariant Metropolis approximations and a proved vanishing rejection estimate; it is not assumed as a final theorem premise.</p>
</details>

<p class="theorem-scope"><strong>Assumption accounting.</strong> The conditional analytic theorem displays its reference argument. The final canonical theorem discharges it using Gibbs normalization and moments, Gaussian Brownian construction, the integral solution, Gibbs stationarity, and concrete extensions of each initial coupling. Noise-law identification and passage to the initial Wasserstein infimum are proved. The theorem does not add a Hessian bound, an unproved stationary-reference assumption, an optimal-coupling assumption, or separate Gibbs moment assumptions.</p>

<h3>The shared proof</h3>
<ol class="proof-roadmap">
<li><a href="#section-sharp-contraction">Contract the deterministic step</a> \(T_h(x)=x-h\nabla U(x)\), with factor \(q=1-mh\) or \(q=Lh-1\).</li>
<li><a href="#section-local-euler-defect">Bound the drift discarded by Euler discretization</a>: its norm is at most \(b=(33/20)Lh\sqrt{hd}\).</li>
<li><a href="#decl-unadjustedlangevin-hilbertdalalyan-l2_reference_bound">Subtract the two updates with shared noise</a>. Cancellation gives \(a_{k+1}\le qa_k+b\), where \(a_k=\|X_k-Y_{k,0}\|_2\).</li>
<li><a href="#section-recurrence">Iterate the scalar inequality</a>, then use the coupling to bound the distance of the laws.</li>
</ol>
\[W_2\bigl(\operatorname{Law}(X_n),\pi\bigr)
 \le a_n\le q^n\|X_0-Y_{0,0}\|_2+\frac{b}{1-q}.\]
<p><a href="#section-initial-coupling">Taking the infimum over finite-cost initial couplings</a> gives the initial term \(q^nW_2(\mu,\pi)\). The same analytic proof handles both regimes; the two results differ in the contraction factor and the simplification of \(b/(1-q)\).</p>
<!--FORMAL_MAIN_STATEMENTS-->
</section>
