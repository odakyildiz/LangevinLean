"""Author the beginner and proof-roadmap cards. No external packages needed."""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
cards = []


def add(key, topic, front, answer, cue, refs=None, code=None, module="01 Lean from zero", kind="lean"):
    card = dict(id=key, module=module, topic=topic, kind=kind, front=front,
                answer=answer, takeaway=cue, refs=refs or [])
    if code:
        card["code"] = dict(file=code[0], start=code[1], end=code[2], side=code[3])
    cards.append(card)


def ref(file, start, end):
    return [dict(file=file, start=start, end=end)]


add("lean-application", "Function application", "How do you read <code>f x</code> and <code>gradient f x</code>?",
    r"<p><code>f x</code> means \(f(x)\). <code>gradient f x</code> means \(\nabla f(x)\).</p><p>Lean applies functions by putting arguments after the function name. <code>iterate g α x₀ n</code> supplies four arguments to <code>iterate</code>; it is the \(n\)-th point of the sequence.</p>",
    "Read spaces between a function and its arguments as application.", ref("Rates.lean",25,27))
add("lean-real-natural", "Number types", "What do <code>ℝ</code>, <code>ℕ</code>, and <code>ℝ≥0</code> mean?",
    r"<p>\(\mathbb R\): real numbers. \(\mathbb N\): natural-number indices, including zero. <code>ℝ≥0</code>: nonnegative real numbers, called <code>NNReal</code>.</p><p>Here the step and strong-convexity constant are real; the Lipschitz constant is stored as a nonnegative real.</p>",
    "The type tells you which objects and operations are available.",ref("Convergence.lean",95,98)+ref("Rates.lean",25,27),code=("Convergence.lean",95,98,"back"))
add("lean-type-colon", "Types and hypotheses", "In <code>(hm : 0 &lt; m)</code>, what does the colon say?",
    r"<p><code>hm</code> is the name of a proof of \(0<m\). The expression after <code>:</code> is its type.</p><p>In <code>(x : H)</code>, the same syntax declares that \(x\) is a point of the space \(H\). A hypothesis is a named proof already available to the current argument.</p>",
    "name : type; a hypothesis has a proposition as its type.",ref("Convergence.lean",95,98))
add("lean-coercion", "Reading a coercion", "Why does the code write <code>(L : ℝ)</code> when <code>L : ℝ≥0</code>?",
    r"<p>It views the nonnegative real \(L\) as an ordinary real number, so it can be used in real arithmetic such as \(2/L\) or \(L\alpha\).</p><p>The notation is a <b>coercion</b>, not an extra assumption and not a new constant. <code>L.coe_nonneg</code> supplies \(0\le (L:\mathbb R)\).</p>",
    "A coercion changes the view of the same value.",ref("Convergence.lean",32,34))
add("lean-vector-operations", "Scalar multiplication", "What is the difference between <code>α * a</code> and <code>α • v</code>?",
    r"<p><code>*</code> is ordinary multiplication of numbers. <code>•</code> scales a vector by a scalar.</p><p>For \(v\in H\), <code>x - α • v</code> is the vector \(x-\alpha v\). In the real line, the lemma <code>smul_eq_mul</code> identifies scalar multiplication with real multiplication.</p>",
    "Use * for scalar arithmetic and • for scaling a vector.",ref("Rates.lean",25,27))
add("lean-norm-inner", "Norm and inner product", "Read <code>‖x - z‖ ^ 2</code> and <code>inner ℝ u v</code> mathematically.",
    r"<p>They mean \(\lVert x-z\rVert^2\) and \(\langle u,v\rangle\), respectively.</p><p>The norm measures distance from zero; \(\lVert x-z\rVert\) measures distance between points. <code>^ 2</code> means a square. The inner product is taken over the real scalar field.</p>",
    "Norms measure size; inner products express directional alignment.",ref("StrongConvexity.lean",40,43))
add("lean-fun", "Anonymous functions", "How do you read <code>fun n ↦ f (x n) - f z</code>?",
    r"<p>It means the function \(n\mapsto f(x_n)-f(z)\), where <code>x n</code> is \(x_n\).</p><p><code>fun</code> constructs a function without giving it a permanent name. The arrow separates the input from the expression for its output. The alternate spelling <code>=&gt;</code> serves the same role in this code.</p>",
    "fun input ↦ output is an anonymous function.",ref("Rates.lean",54,54))
add("lean-theorem-goal", "A theorem and its goal", "What starts after <code>:= by</code> in a theorem?",
    "<p>A tactic proof of the proposition stated before it. The <b>goal</b> is the proposition still to be proved; local hypotheses are proofs you can use.</p><p>A tactic transforms the goal or supplies a proof. Lean checks the resulting proof term with its kernel.</p>",
    "The theorem states a proposition; by starts its proof.",ref("StrongConvexity.lean",22,24),code=("StrongConvexity.lean",22,24,"back"))
add("lean-explicit-implicit", "Implicit arguments", "What changes when a parameter uses braces, as in <code>{m : ℝ}</code>?",
    "<p>It is an <b>implicit</b> parameter: Lean normally infers it from the other arguments or from the goal.</p><p>Parentheses such as <code>(hm : 0 &lt; m)</code> make an argument explicit. Neither style removes the parameter from the mathematical statement.</p>",
    "Braces ask Lean to infer; parentheses normally ask you to supply.",ref("Convergence.lean",95,98))
add("lean-typeclasses", "The ambient space", "What do the square-bracketed assumptions in this source line supply?",
    r"<p>Vector addition, subtraction and a norm; a real inner product; and completeness. Together these give the real Hilbert-space setting.</p><p>Square brackets ask Lean's <b>instance search</b> to find the mathematical structures and facts that operations and library lemmas need.</p>",
    "Square brackets supply the mathematical structure of the space.",ref("Convergence.lean",24,24),code=("Convergence.lean",24,24,"front"))
add("lean-have-let", "A definition versus a proved fact", "What is the difference between <code>let</code> and <code>have</code>?",
    r"<p><code>let</code> introduces a local definition, such as \(d=y-x\). <code>have</code> introduces a proved local fact, such as a derivative formula or an inequality.</p><p><code>have h : P := by ...</code> opens a subproof of \(P\), then stores its proof as <code>h</code>.</p>",
    "let names an expression; have records a proved fact.",ref("Smooth.lean",29,38),code=("Smooth.lean",29,31,"back"))
add("lean-exact", "Finish with an existing proof", "What does <code>exact h</code> do?",
    "<p>It finishes the current goal with the proof <code>h</code>, provided the type of <code>h</code> matches the goal.</p><p>Likewise, <code>exact lemma arg₁ arg₂</code> applies the lemma to its arguments and supplies the resulting proof. It does not perform arbitrary simplification.</p>",
    "exact supplies a proof of precisely the current goal.",ref("Smooth.lean",62,66),code=("Smooth.lean",64,64,"back"))
add("lean-apply", "Work backward from a lemma", "What does <code>apply lemma</code> do to a goal?",
    "<p>It matches the lemma's conclusion to your goal. Any premises you have not supplied become new goals.</p><p>For a product, <code>apply mul_nonneg</code> asks for both signs. In this snippet <code>hα.le</code> already supplies the first, so only the second sign remains to be proved.</p>",
    "apply replaces the goal by the lemma's missing premises.",ref("Convergence.lean",76,78),code=("Convergence.lean",76,78,"back"))
add("lean-rw", "Rewrite an expression", "What does <code>rw [lemma] at h</code> change?",
    "<p>It replaces an expression in the hypothesis <code>h</code> using the named equality or equivalence. Without <code>at h</code>, it rewrites the goal.</p><p>A left arrow, as in <code>rw [← lemma]</code>, reverses the direction. In the snippet, the norm identity is rewritten inside <code>hxy</code>.</p>",
    "rw changes an expression by a proved identity.",ref("StrongConvexity.lean",64,66),code=("StrongConvexity.lean",64,66,"back"))
add("lean-simp", "Simplify", "What does <code>simp only [lemmas]</code> mean?",
    "<p>Simplify using the listed lemmas and basic definitional reduction. The word <code>only</code> restricts the additional rewrite rules used.</p><p>Typical simplifications evaluate zero scalar multiples, remove additions of zero, or unfold a function application. They are justified by identities, not guesses.</p>",
    "simp only uses a controlled collection of simplifications.",ref("Smooth.lean",68,70),code=("Smooth.lean",68,70,"back"))
add("lean-simpa", "Simplify and use a proof", "What does <code>simpa using h</code> combine?",
    "<p>It simplifies the goal and the type of <code>h</code>, then uses <code>h</code> to prove the simplified goal.</p><p>It is useful when a library lemma proves the desired statement in a slightly different notation, such as a distance instead of a norm.</p>",
    "simpa = simplify the two statements until the supplied proof fits.",ref("Step.lean",61,62),code=("Step.lean",61,62,"back"))
add("lean-change-dsimp", "Unfolding definitions", "How do <code>change</code> and <code>dsimp</code> help read a proof?",
    "<p><code>change P</code> presents the goal in a definitionally equal form. <code>dsimp [definitions]</code> unfolds the named definitions and reduces expressions.</p><p>They expose what notation means. They do not prove a new analytic inequality; the underlying proposition remains the same.</p>",
    "Unfold definitions to reveal the mathematical expression.",ref("StrongConvexity.lean",28,31)+ref("Smooth.lean",56,56),code=("StrongConvexity.lean",28,31,"back"))
add("lean-constructor", "Split a conjunction", "If the goal is <code>P ∧ Q</code>, what does <code>constructor</code> ask for?",
    "<p>Two proofs: first of <code>P</code>, then of <code>Q</code>. The bullets <code>·</code> organize the separate subproofs.</p><p>In <code>stationary_unique_minimizer</code>, the components are global minimality and uniqueness. Each component needs its own argument.</p>",
    "To prove P ∧ Q, prove both P and Q.",ref("Minimizer.lean",43,48),code=("Minimizer.lean",43,48,"back"))
add("lean-intro", "Introduce an input or premise", "What does <code>intro</code> do for <code>∀ x, P x</code> and <code>P → Q</code>?",
    "<p>For a universal statement, it introduces an arbitrary input <code>x</code> and asks you to prove <code>P x</code>.</p><p>For an implication, it assumes a proof of <code>P</code> and asks you to prove <code>Q</code>. <code>intro y hy</code> can do both in succession.</p>",
    "intro moves an arbitrary input or assumed premise into the context.",ref("Minimizer.lean",43,49))
add("lean-obtain", "Extract a witness", "What does the displayed <code>obtain</code> line give the proof?",
    r"<p>A point \(z\in H\) and a named proof <code>hz</code> of \(\nabla f(z)=0\).</p><p><code>exists_stationary</code> proves that such a point exists. The angle-bracket pattern extracts its witness and accompanying proof so later steps can use them.</p>",
    "obtain unpacks an existential witness and its proved properties.",ref("Convergence.lean",109,109),code=("Convergence.lean",109,109,"front"))
add("lean-refine-holes", "Build a proof with remaining goals", "What do the two <code>?_</code> placeholders in this <code>refine</code> line mean?",
    "<p>Two proof goals remain. The already named facts supply stationarity, minimality, uniqueness and the limits; <code>hgap n</code> supplies nonnegativity.</p><p>The holes ask for the geometric gap bound and squared-distance bound at each natural number <code>n</code>. An underscore <code>_</code> elsewhere often asks Lean to infer an ordinary argument.</p>",
    "refine fills the proof structure and leaves explicit proof holes.",ref("Convergence.lean",122,128),code=("Convergence.lean",124,124,"front"))
add("lean-quantifiers", "Logical symbols", "Read <code>∀</code>, <code>∃</code>, <code>∃!</code>, <code>∧</code>, <code>→</code>, and <code>¬</code>.",
    "<p><code>∀</code>: for every. <code>∃</code>: there exists. <code>∃!</code>: there exists exactly one. <code>∧</code>: and. <code>→</code>: implies (or a function type, depending on its arguments). <code>¬</code>: not.</p><p>The symbol describes what sort of proof is required: all inputs, a witness, multiple components, an implication, or a contradiction.</p>",
    "Logical notation tells you how to construct the proof.",ref("Convergence.lean",99,108))
add("lean-iff-directions", "Directions of an equivalence", "For a theorem <code>P ↔ Q</code>, what do <code>.mp</code> and <code>.mpr</code> do?",
    r"<p><code>.mp</code> takes a proof of \(P\) to a proof of \(Q\). <code>.mpr</code> goes from \(Q\) to \(P\).</p><p>For example, <code>sub_nonneg.mpr</code> turns \(f(z)\le f(x)\) into \(0\le f(x)-f(z)\). The direction matters.</p>",
    "mp goes forward through ↔; mpr goes backward.",ref("Convergence.lean",119,119),code=("Convergence.lean",119,119,"back"))
add("lean-projections", "Projection notation", "What do <code>.1</code> and <code>.2</code> select in this proof?",
    r"<p>For a conjunction or pair, they select its first or second component. Here membership in \([0,1]\) includes both endpoint inequalities; <code>.1</code> supplies \(0\le t\).</p><p>The same suffixes on an equivalence can select its forward or backward implication. Read the type to know which meaning is being used.</p>",
    "A projection selects one component of an already proved structured fact.",ref("Smooth.lean",47,50),code=("Smooth.lean",47,50,"back"))
add("lean-trans", "Chain inequalities", "If <code>h₁</code> proves <code>A ≤ B</code> and <code>h₂</code> proves <code>B ≤ C</code>, what does <code>h₁.trans h₂</code> prove?",
    r"<p>\(A\le C\), by transitivity.</p><p>The shared middle expression \(B\) must match. The code repeatedly uses this to compose an analytic inequality with an arithmetic bound, rather than reproving the entire chain at once.</p>",
    "trans joins two inequalities through a shared middle expression.",ref("Rates.lean",75,75),code=("Rates.lean",75,75,"back"))
add("lean-linear-arithmetic", "linarith", "What mathematical work is <code>linarith</code> doing in this development?",
    "<p>It combines and rearranges available real linear inequalities after normalization. It can, for example, add the two strong first-order inequalities and cancel the function values.</p><p>It does not invent strong convexity or differentiation facts; those must already have been proved and supplied.</p>",
    "Provide the analytic inequalities; linarith checks the linear rearrangement.",ref("StrongConvexity.lean",64,72))
add("lean-nonlinear-arithmetic", "nlinarith", "Why do some proofs explicitly give <code>sq_nonneg ...</code> to <code>nlinarith</code>?",
    "<p><code>nlinarith</code> normalizes polynomial expressions and reasons with arithmetic facts. A supplied nonnegative square is an important extra inequality.</p><p>In the gap upper bound, the square of <code>m * ‖z - x‖ - ‖gradient f x‖</code> provides the completed-square argument. The tactic checks its algebraic consequence.</p>",
    "A nonnegative square often supplies the missing polynomial inequality.",ref("StrongConvexity.lean",94,96),code=("StrongConvexity.lean",94,96,"back"))
add("lean-ring-positivity", "Algebra and signs", "What is the difference between <code>ring</code> and <code>positivity</code>?",
    "<p><code>ring</code> proves polynomial identities by normalization: two algebraic expressions are equal.</p><p><code>positivity</code> proves sign goals using known signs, positive constants, squares and norms. An inequality needs its sign assumptions; an identity does not.</p>",
    "ring checks an identity; positivity checks a sign.",ref("Rates.lean",43,46))
add("lean-definitional-equality", "rfl and recursion", "Why can <code>rfl</code> prove the zeroth-iterate theorem?",
    "<p>The zero branch of <code>iterate</code> is defined to be <code>x₀</code>. Unfolding that definition makes both sides literally the same expression.</p><p><code>rfl</code> uses this definitional equality. The attribute <code>@[simp]</code> registers the proved identity for later simplification.</p>",
    "rfl proves equality when unfolding definitions makes both sides identical.",ref("Rates.lean",25,30),code=("Rates.lean",29,30,"front"))
add("lean-convert", "A nearly matching proof", "What does <code>convert h using 1</code> do?",
    "<p>It uses <code>h</code> as a candidate proof and creates equality goals for the expressions that differ at the requested level.</p><p>In the derivative calculation, the remaining goals check the function expression and the derivative expression. Unfolding, pointwise equality and <code>ring</code> discharge those checks.</p>",
    "convert isolates the equalities needed to make a candidate proof fit.",ref("Smooth.lean",39,46),code=("Smooth.lean",41,42,"back"))
add("lean-extensionality", "Equality of functions", "Why do <code>ext s</code> or <code>funext x</code> help prove functions equal?",
    "<p>Two functions are equal when their outputs agree at every input. These commands introduce an arbitrary input and reduce the function-equality goal to pointwise equality.</p><p>The polynomial derivative construction uses <code>ext s</code> to compare the two functions at an arbitrary real parameter <code>s</code>.</p>",
    "Prove functions equal by proving their values equal at every input.",ref("Smooth.lean",43,44),code=("Smooth.lean",43,44,"back"))
add("lean-library-methods", "Reading a dot after a proof", "What does <code>(hq t).continuousAt</code> mean?",
    "<p>Apply a library lemma to the proved derivative fact <code>hq t</code>: a function with a derivative at a point is continuous there.</p><p>A dot often lets you use a proof as the first argument of another theorem. Here <code>.differentiableAt</code> and <code>.deriv</code> similarly extract consequences of the derivative statement.</p>",
    "A proved derivative supplies continuity, differentiability and its derivative value.",ref("Smooth.lean",59,66))
add("lean-noncomputable", "Classical constructions", "Does <code>noncomputable section</code> mean that a proof is missing?",
    "<p>No. It permits definitions built from classical constructions, such as choosing the Riesz representative that defines a gradient.</p><p>The theorems still need complete proofs checked by Lean. This project contains no proof admissions; its axiom audit lists the standard logical foundations used by Mathlib.</p>",
    "noncomputable permits classical definitions; it does not admit a theorem.",ref("Convergence.lean",17,24))
add("lean-rwa", "Rewrite and finish", "What extra work does <code>rwa</code> do compared with <code>rw</code>?",
    "<p>It rewrites and then tries to finish by using an available proof. In the square-root bound, the rewrite changes <code>hbound</code> into exactly the desired norm inequality, so that hypothesis closes the goal.</p><p>The displayed rules split the square root of a product and replace the square root of a nonnegative norm squared by the norm.</p>",
    "rwa rewrites, then closes with the matching proof.",ref("Step.lean",41,43),code=("Step.lean",41,43,"back"))
add("lean-field-simp", "Clear denominators", "What does <code>field_simp</code> check in the squared-distance bound?",
    r"<p>It clears denominators in the remaining field-algebra equality. Here the equality is \(B/(m/2)=(2/m)B\), with \(m>0\) so the relevant denominators are nonzero.</p><p>The order-sensitive division was already justified by a positive-denominator lemma. <code>field_simp</code> handles the equality of the resulting expressions; it does not supply the analytic bound.</p>",
    "Justify division in an inequality first; then clear denominators in the algebra.",ref("Rates.lean",75,79),code=("Rates.lean",78,79,"back"))
add("lean-norm-num", "Numerical facts", "What does <code>norm_num</code> contribute to the endpoint proofs?",
    r"<p>It verifies arithmetic facts about explicit numerals and normalizes numerical expressions. After uniqueness of limits would force \(1=0\), <code>norm_num at heq</code> detects that the hypothesis <code>heq</code> is impossible.</p><p>It also proves routine facts such as \(0\le1\) or \(2\ne0\); the nontrivial convergence reasoning comes from earlier lemmas.</p>",
    "norm_num checks explicit arithmetic; it does not prove the convergence theorem.",ref("Sharpness.lean",80,81),code=("Sharpness.lean",80,81,"back"))
add("lean-strict-to-weak", "Use a strict sign as a weak sign", "If <code>hα</code> proves <code>0 &lt; α</code>, what does <code>hα.le</code> prove?",
    r"<p>\(0\le\alpha\). A strictly positive quantity is also nonnegative.</p><p>Many multiplication lemmas only need a weak sign to preserve order. The code keeps the stronger assumption for other steps, but uses <code>.le</code> to supply precisely the weaker premise a particular lemma asks for.</p>",
    "A strict inequality has its corresponding weak inequality as .le.",ref("Convergence.lean",76,78),code=("Convergence.lean",76,78,"back"))


def overview(key, topic, front, answer, cue, refs):
    add(key,topic,front,answer,cue,refs,module="02 Proof roadmap",kind="checkpoint")


overview("map-assumptions", "The complete hypothesis list", "What hypotheses guarantee convergence in this formalization?",
    r"<p>\(H\) is a complete real inner-product space. \(f:H\to\mathbb R\) is differentiable everywhere and \(m\)-strongly convex, with \(m>0\). Its gradient is \(L\)-Lipschitz, with \(L>0\).</p><p>The fixed step satisfies \(0<\alpha<2/L\). The starting point \(x_0\) is arbitrary. A minimizer is <b>proved to exist</b>, not assumed.</p>",
    "Hilbert space + differentiable + strong convexity + Lipschitz gradient + strict step interval.",ref("Convergence.lean",95,98))
overview("map-gradient-derivative", "Gradient versus derivative", "How does the gradient connect a derivative to inner-product inequalities?",
    r"<p>The derivative \(Df(x)\) is a continuous linear map. The gradient is its representing vector:</p>\[Df(x)[v]=\langle\nabla f(x),v\rangle.\]<p>Mathlib supplies this identity as <code>inner_gradient_left</code>. It is the bridge from differentiation to the vector inequalities used in gradient descent.</p>",
    "The gradient represents the derivative by an inner product.",ref("StrongConvexity.lean",50,57))
overview("map-two-constants", "What m and L control", "What do the constants m and L control, and which bounds do they produce?",
    r"<p>\(m\) gives a quadratic <b>lower</b> model:</p>\[\begin{aligned}f(y)\ge{}&f(x)+\langle\nabla f(x),y-x\rangle\\&+\tfrac m2\lVert y-x\rVert^2.\end{aligned}\]<p>\(L\) gives the matching quadratic <b>upper</b> model, replacing \(m\) by \(L\) and reversing the inequality. Lower control yields gap/distance bounds; upper control yields descent.</p>",
    "m controls the lower model; L controls the upper model.",ref("StrongConvexity.lean",40,43)+ref("Smooth.lean",26,28))
overview("map-gradient-update", "The actual algorithm", "State the gradient descent update and the symbols used for one step.",
    r"\[x_{n+1}=x_n-\alpha\nabla f(x_n).\]<p>For a generic current point \(x\), write \(G=\nabla f(x)\) and \(x^+=x-\alpha G\). The subtraction moves against the gradient. The step \(\alpha\) stays fixed throughout the sequence.</p>",
    "Current point minus step times gradient gives the next point.",ref("Rates.lean",25,34))
overview("map-four-links", "The central proof chain", "After finding a stationary minimizer z, what four links give convergence?",
    r"<p>Set \(\Delta_n=f(x_n)-f(z)\).</p><ol><li>Strong convexity: \(\tfrac m2\lVert x_n-z\rVert^2\le\Delta_n\).</li><li>One-step descent plus the gradient gap bound: \(\Delta_{n+1}\le\rho\Delta_n\).</li><li>Induction: \(\Delta_n\le\rho^n\Delta_0\).</li><li>For \(0\le\rho<1\), geometric decay and the lower bound force \(x_n\to z\).</li></ol>",
    "Lower gap → one-step contraction → geometric decay → norm convergence.",ref("Convergence.lean",111,121))
overview("map-rho", "The rate to remember", "What is the geometric objective-gap factor in the Lean theorem?",
    r"\[\rho=\max\{0,1-m\alpha(2-L\alpha)\}.\]<p>The assumptions give \(0\le\rho<1\). If \(m\le L\), the raw expression is nonnegative and the maximum can be removed. The code uses the maximum so it does not require that additional parameter comparison.</p>",
    "Remember the clamped rate, then the simpler formula when m ≤ L.",ref("Convergence.lean",26,54))
overview("map-gap-distance-rates", "The two finite bounds", "Given Δ₀=f(x₀)-f(z), what are the objective-gap and squared-distance rates?",
    r"\[0\le f(x_n)-f(z)\le\rho^n\Delta_0.\]\[\lVert x_n-z\rVert^2\le\frac2m\rho^n\Delta_0.\]<p>These are finite bounds for every natural number \(n\). The second comes from solving the strong-convexity lower-gap inequality for squared distance.</p>",
    "The gap decays as ρⁿ; the squared distance is at most (2/m) times that bound.",ref("Convergence.lean",104,108))
overview("map-two-steps", "Two step sizes with different jobs", "Does minimizer existence restrict the actual gradient-descent step to αL²&lt;2m?",
    r"<p>No. Existence uses an <b>auxiliary</b> positive step \(\beta=m/(L^2+m^2)\) to make a contraction and obtain a stationary point. In that local Lean proof the symbol is also named <code>α</code>.</p><p>The actual sequence has its own step \(\alpha\), and the full convergence theorem allows every \(0<\alpha<2/L\).</p>",
    "Auxiliary contraction proves existence; the actual step needs only 0 < α < 2/L.",ref("Minimizer.lean",20,37)+ref("Convergence.lean",95,98))
overview("map-sign-checks", "The sign checks behind the proof", "Which signs must you check before chaining the rate argument?",
    r"<p>\(m>0\) permits positive division. \(L>0\) permits turning \(\alpha<2/L\) into \(L\alpha<2\). The interval gives \(c=\alpha(1-L\alpha/2)>0\), so the gradient gap bound can be scaled.</p><p>\(\Delta\ge0\) permits replacing the raw factor by \(\rho\), and \(\rho\ge0\) permits the induction step.</p>",
    "Positive division and order-preserving multiplication need their sign proofs.",ref("Convergence.lean",75,91)+ref("Rates.lean",37,46))
overview("map-proof-reconstruction", "Reconstruct the whole argument", "In one breath, reconstruct the full proof from assumptions to the limits.",
    r"<p>Strong convexity gives monotonicity and two gap bounds. An auxiliary contraction gives a stationary point, hence the unique minimizer. Lipschitz gradient gives the quadratic upper model and descent. Combine descent with \(2m\Delta\le\lVert\nabla f(x)\rVert^2\) to contract the gap.</p><p>Induction gives \(\rho^n\Delta_0\); squeezing gives zero gap and zero distance. Thus \(x_n\to z\) and \(f(x_n)\to f(z)\).</p>",
    "Existence first; local inequalities next; scalar decay and limits last.",ref("Convergence.lean",109,128))

(HERE / "cards_foundations.json").write_text(json.dumps({"cards":cards}, ensure_ascii=False, indent=2)+"\n")
print(f"Wrote {len(cards)} beginner and roadmap cards.")
