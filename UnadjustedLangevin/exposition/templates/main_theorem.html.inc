<section class="main-theorem" id="main-theorem" aria-labelledby="main-theorem-title">
<h2 id="main-theorem-title">Main theorem. Gaussian ULA for a strongly convex potential</h2>
<p class="theorem-plain">The theorem bounds the quadratic Wasserstein distance between the ULA distribution and the Gibbs measure. The assumptions on the potential are differentiability, strong convexity and a Lipschitz gradient. The proof establishes Gibbs normalization, the required moments and stationarity, and then uses a coupling with a stationary Langevin process.</p>
<p class="reading-note">The separate <a href="../../LSI/exposition/index.html">ULA under LSI report</a> proves an entropy estimate from a log-Sobolev inequality, a Lipschitz gradient and finite initial relative entropy. That proof establishes the Gaussian density regularity and the entropy estimates at positive times and near zero.</p>

<p>The coupling argument is stated in a Hilbert space and then applied to Euclidean random vectors. IPLA uses the same estimate for its particle potential in scaled coordinates. The <a href="#module-unadjustedlangevin-canonicalula-lean">complete source</a> supplies the final Gaussian ULA theorem.</p>
<h3>The algorithm and its assumptions</h3>
<p>Let \(d\ge1\), and let \(U:\mathbb R^d\to\mathbb R\) be differentiable and \(m\)-strongly convex, with \(L\)-Lipschitz gradient, where \(0<m\le L\). Its Gibbs probability measure is</p>
\[\pi(dx)=Z^{-1}e^{-U(x)}dx,\qquad Z=\int_{\mathbb R^d}e^{-U(x)}dx\in(0,\infty).\]
<p>Let \(X_0\) have law \(\mu\), with finite second moment. Let the innovations \(\xi_k\) be independent standard Gaussian vectors, independent of \(X_0\). For a step \(h>0\), define</p>
\[X_{k+1}=X_k-h\nabla U(X_k)+\sqrt{2h}\,\xi_k.\]
<p>Let \(P_h(x,\cdot)=\mathcal N(x-h\nabla U(x),2hI_d)\). Conditioning on the current state gives \(\mu_n=\mu P_h^n\). Thus the iterated measure transition and the displayed stochastic recursion have the same distributions. Set</p>
\[C_0=W_2(\mu,\pi).\]
<p>Strong convexity gives Gaussian domination of the unnormalized Gibbs density, proving that its normalizing constant is finite and positive and that its second moment is finite. The product coupling of this measure with the initial measure then has finite quadratic cost, so \(C_0<\infty\).</p>

<h3>Conclusion, for every iteration count \(n\in\mathbb N\)</h3>
<p><strong>Small-step case:</strong> if \(0<h\le 2/(m+L)\), then</p>
\[\boxed{W_2\bigl(\operatorname{Law}(X_n),\pi\bigr)
 \le (1-mh)^n W_2(\mu,\pi)+1.65\,\frac{L}{m}\sqrt{hd}.}\]
<p class="theorem-proof-link"><a href="#decl-unadjustedlangevin-hilbertdalalyan-dalalyan_small_step_of_integral_reference">Read the shared proof and its Lean notes</a> · formal statement <code>ULA.Hilbert.dalalyan</code></p>
<p><strong>Large-step case:</strong> if \(2/(m+L)\le h<2/L\), then</p>
\[\boxed{W_2\bigl(\operatorname{Law}(X_n),\pi\bigr)
 \le (Lh-1)^n W_2(\mu,\pi)+1.65\,\frac{Lh}{2-Lh}\sqrt{hd}.}\]
<p class="theorem-proof-link"><a href="#decl-unadjustedlangevin-hilbertdalalyan-dalalyan_large_step_of_integral_reference">Read the shared proof and its Lean notes</a> · formal statement <code>ULA.Hilbert.dalalyan_large_step</code></p>
<p>The coefficient \(1.65\) is the exact rational number \(33/20\). The upper bound \(h<2/L\) in the large-step case is strict. The two formulas agree at \(h=2/(m+L)\).</p>

<h3>Meaning of the terms in the estimate</h3>
<p>For probability measures with finite second moments, \(W_2(\mu,\nu)\) is the infimum of \(\bigl(\int\|x-y\|^2d\gamma(x,y)\bigr)^{1/2}\) over all couplings \(\gamma\) of \(\mu\) and \(\nu\). The initial term is this infimum. The proof applies to every finite-cost initial coupling and does not require an optimal coupling.</p>
<p>In each stated step interval, the contraction factor \(q\), equal to \(1-mh\) or \(Lh-1\), satisfies \(0\le q<1\). Hence the contribution \(q^nC_0\) from the initial distribution tends to zero as \(n\to\infty\).</p>
<p>The remaining term is an upper bound for the accumulated discretization error. It is independent of \(n\), and is proportional to \(\sqrt h\) in the small-step case. For fixed \(h>0\), the convergence estimate therefore gives a nonzero limiting upper bound; it does not prove convergence to the exact Gibbs measure at that fixed step.</p>

<details class="reference-assumptions" id="main-reference-assumptions">
<summary>The stationary reference and its assumptions</summary>
<p>The analytic stage uses continuous curves \(Y_{k,t}\) in \(L^2(P;\mathbb R^d)\), with noise increments \(B_{k,t}\). For \(0\le t\le h\), they satisfy</p>
\[Y_{k,t}-Y_{k,0}=-\int_0^t\nabla U(Y_{k,s})\,ds+B_{k,t},\]
\[\|\nabla U(Y_{k,t})\|_2\le\sqrt{Ld},\qquad
  \|B_{k,t}\|_2\le\sqrt{2d}\sqrt t.\]
<p>The final value of one segment is the initial value of the next. The noise at the end of the segment is the Gaussian increment in the recursion, and the reference distribution is stationary:</p>
\[Y_{k,h}=Y_{k+1,0},\qquad B_{k,h}=\sqrt{2h}\,\xi_k,
 \qquad\operatorname{Law}(Y_{k,0})=\pi.\]
<p>These equalities hold in \(L^2\). The <a href="#decl-unadjustedlangevin-hilbertdalalyan-L2Reference">conditional comparison theorem</a> assumes the stated reference properties. The final ULA theorem proves their existence. For stationarity, the proof uses invariant Metropolis approximations and bounds the expected rejected displacement so that it tends to zero with the time mesh.</p>
</details>

<p class="theorem-scope">The final theorem derives the reference properties from the assumptions on the potential and the independent Gaussian innovations. It proves normalization and moments, constructs the Gaussian process and integral solution, proves Gibbs stationarity, and extends each initial coupling independently of the Gaussian variables. Its estimate holds uniformly over these couplings, so taking their infimum gives the initial Wasserstein term. No Hessian or optimal-coupling assumption is required.</p>

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
