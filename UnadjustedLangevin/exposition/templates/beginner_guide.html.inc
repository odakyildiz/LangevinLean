<details class="beginner-guide" id="lean-beginner-guide" open>
<summary>Lean syntax, proof states, and symbol entry</summary>
<div class="guide-body">
<p>This guide defines the notation and proof commands used in the source excerpts. It assumes no prior experience with Lean. Each proof block also has an explanation of its individual source lines and arguments. The examples in this guide illustrate the syntax; the numbered source boxes elsewhere reproduce the repository code.</p>
<p>The topics are ordered as follows: types and proofs, goals, local definitions and intermediate results, function application, affine maps, and simplification. The symbol table gives the corresponding keyboard abbreviations.</p>

<details class="guide-topic" id="lean-types">
<summary>Types, values, propositions, and the colon <code>:</code></summary>
<p>A <em>type</em> tells Lean what kind of object an expression is. <code>x : ℝ</code> says that <code>x</code> is a real number. <code>f : H → ℝ</code> says that <code>f</code> takes an element of the space <code>H</code> and returns a real number. <code>x y : H</code> introduces two elements, both belonging to <code>H</code>. These names are placeholders for arbitrary objects; no numerical value is being chosen.</p>
<p>A mathematical assertion is also a type, specifically a <em>proposition</em>. In <code>hx : 0 ≤ x</code>, the name <code>hx</code> denotes a proof that <code>x</code> is nonnegative. The name <code>x</code> denotes a number, while <code>hx</code> denotes evidence for an assertion about that number. The initial <code>h</code> is an author’s naming convention, not a Lean keyword. You could rename <code>hx</code> to <code>x_nonnegative</code>.</p>
<p>This explains why the same colon appears in <code>line : ℝ →ᵃ[ℝ] H</code> and <code>hc : ConvexOn ℝ Set.univ (f ∘ line)</code>. The first specifies the type of a mathematical object. The second specifies the proposition proved by <code>hc</code>. A complete theorem supplies a proof with the type written after its final colon.</p>
<p><code>Type*</code> in a variable declaration allows an arbitrary universe level for a type such as <code>H</code>. It does not mean multiplication. <code>Prop</code> is the sort of propositions. You usually do not need to manipulate universe levels to read these proofs. Parenthesized expressions such as <code>(0 : ℝ)</code> explicitly specify which type a numeral has, since <code>0</code> could otherwise be a natural number, a real number, or the zero vector of a space.</p>
</details>

<details class="guide-topic" id="lean-goals">
<summary>Goals, <code>by</code> blocks, indentation, and <code>⊢</code></summary>
<p>A <em>goal</em> is the statement Lean is currently asking you to prove. The <em>context</em> is the collection of objects and facts available at that point. In the Lean editor, the Infoview displays them, for example:</p>
<pre class="note-code">x : ℝ
hx : 0 ≤ x
⊢ 0 ≤ x + 0</pre>
<p>The lines above <code>⊢</code> say that <code>x</code> is a real number and <code>hx</code> proves its nonnegativity. The expression after <code>⊢</code> is the current target. The turnstile is normally displayed by Lean; you do not insert this proof-state display into the source file.</p>
<p><code>by</code> starts a block of <em>tactics</em>: instructions that construct a proof of the expected statement. Indentation indicates which instructions belong to that block. In a proof containing <code>have hc : P := by</code>, the more deeply indented block proves the temporary target <code>P</code>. When it finishes and indentation returns to the outer level, the previous goal is restored and <code>hc : P</code> is now available.</p>
<p>Some tactics replace one goal by several smaller goals. The bullet <code>·</code> focuses one of those subgoals, with its own indented proof. A newline may also simply continue a long expression. For example, an indented list of arguments following <code>simpa using</code> is still part of the same command. The line-by-line notes point out these continuation lines.</p>
<p>Place the editor cursor after a tactic to see the resulting state; place it before the tactic to see the input state. This is how to inspect what simplification or rewriting actually did. The mathematical proof beside the code describes its role; the editor shows the precise generated goals.</p>
</details>

<details class="guide-topic" id="lean-assignment">
<summary>Types, definitions, and equality: <code>:</code>, <code>:=</code>, and <code>=</code></summary>
<p><code>:</code> introduces a type or proposition. <code>:=</code> introduces the expression that supplies its value or proof. Read <code>let n : ℕ := 3</code> as “define the local natural number <code>n</code> to be <code>3</code>.” Read <code>have h : 0 ≤ n := someProof</code> as “name this proof of <code>0 ≤ n</code> by <code>h</code>.”</p>
<p>In <code>lemma myLemma : P := by …</code>, the text after <code>:=</code> must be a proof of <code>P</code>. The <code>by</code> block builds that proof through tactics. In <code>let line : ℝ →ᵃ[ℝ] H := AffineMap.lineMap x y</code>, the text after <code>:=</code> is an affine-map object. In both cases Lean checks that the right-hand expression has the specified type.</p>
<p><code>=</code> is different: it forms a mathematical assertion of equality. <code>line = anotherMap</code> is something that could need a proof. Writing <code>:=</code> gives a definition or a proof term; it is not an instruction to prove an equality and does not mutate an earlier variable. Local definitions are not changing computer storage as the argument runs.</p>
<p>The colon and equals sign in <code>:=</code> are ordinary keyboard characters typed together. The Unicode typing machinery is not needed for them. You can often omit an explicit type, as in <code>have hs := someTheorem arguments</code>, because Lean can infer the type of the expression on the right.</p>
</details>

<details class="guide-topic" id="lean-let">
<summary>Local definitions with <code>let</code> and their expansion</summary>
<p><code>let</code> gives a local name to a specified value. In the first proof, <code>let line : ℝ →ᵃ[ℝ] H := AffineMap.lineMap x y</code> introduces the abbreviation <code>line</code> for that particular affine map. The name is usable in the remainder of this proof, including its nested subproofs. It is not a new hypothesis asserting that some unspecified map exists.</p>
<p>A local definition retains its defining value. <em>Unfolding</em> it means replacing occurrences of its name by that value. Thus unfolding <code>line</code> replaces it by <code>AffineMap.lineMap x y</code>. This replacement is justified by the definition itself; there is no extra mathematical lemma to prove.</p>
<p>Here is a small checked example:</p>
<pre class="note-code">example : (3 : ℕ) + 0 = 3 := by
  let n : ℕ := 3
  have hn : n + 0 = 3 := by
    simp [n]
  simpa [n] using hn</pre>
<p>The local object <code>n</code> has value <code>3</code>. The intermediate proposition <code>hn</code> mentions that name. The final command unfolds it and uses <code>hn</code> to finish the outer goal. The definition did not change the outer goal to a different theorem; it supplied a convenient abbreviation used while proving it.</p>
</details>

<details class="guide-topic" id="lean-have">
<summary>Intermediate results with <code>have</code></summary>
<p><code>have</code> introduces an intermediate result after you supply its justification. In <code>have hc : P := by …</code>, you choose a name <code>hc</code>, state the proposition <code>P</code>, and prove it in the indented block. After that block succeeds, later lines can use <code>hc</code>. You have not asked Lean to accept <code>P</code> without evidence.</p>
<pre class="note-code">example (x : ℝ) (hx : 0 ≤ x) : 0 ≤ x + 0 := by
  have h : 0 ≤ x := hx
  simpa using h</pre>
<p><code>hx</code> is a supplied hypothesis; <code>h</code> is a new local name for a proof obtained from it. The word <code>have</code> is not English prose ignored by Lean: it is syntax that adds a checked local declaration to the context. The last line simplifies the new fact and the target so that they match.</p>
<p>You can write <code>have hs := theoremName arguments</code> without a colon. Lean reads the theorem’s result type and infers which proposition <code>hs</code> proves. You can also introduce a parameterized local result: <code>have hbound (t : ℝ) : P t := by …</code>. That proves a fact available for every real argument <code>t</code>; later <code>hbound s</code> applies it at <code>s</code>.</p>
<p>The first proof’s <code>hc</code>, <code>hl</code>, <code>hd</code>, and <code>hs</code> are chosen names: convexity of the restriction, its line derivative, the derivative of its composition, and the slope inequality. Their spelling conveys the author’s intent but does not change Lean’s logic. The type after the colon determines what each fact actually says.</p>
<p><strong>Comparison with <code>let</code>:</strong> in ordinary proof writing, <code>have</code> usually names a proved proposition and <code>let</code> usually names a defined mathematical object. This is a convention, not a restriction saying one can only hold proofs and the other can only hold data. Both introduce typed local terms. A <code>let</code> binding retains a defining value that can be unfolded; a fact introduced with <code>have</code> is normally used through its stated type. For the first proof, use <code>let line</code> to abbreviate the map and <code>have hc</code> to record the proved convexity of its composition.</p>
</details>

<details class="guide-topic" id="lean-application">
<summary>Function application, function definitions, and composition</summary>
<p>Lean normally applies a function by writing its name followed by its arguments, separated by spaces. <code>f x</code> means the mathematical expression <em>\(f(x)\)</em>. <code>AffineMap.lineMap x y</code> applies the named construction first to <code>x</code> and then to <code>y</code>. A function expecting several arguments can be applied to just its first arguments, producing a function that awaits the rest.</p>
<p>Application groups to the left: <code>f x y</code> means <code>(f x) y</code>. Parentheses group an argument that is itself an expression. <code>f (x + y)</code> applies <code>f</code> to the sum; <code>f x + y</code> adds <code>y</code> after applying <code>f</code>. Similarly, <code>gradient f x</code> means “the gradient of <code>f</code> evaluated at <code>x</code>,” and <code>inner ℝ u v</code> specifies the real inner product of two vectors.</p>
<p><code>fun t ↦ expression</code> defines a function by describing its value at a variable input. The ASCII version <code>fun t =&gt; expression</code> has the same role. For example, <code>fun t : ℝ ↦ t • (y - x) + x</code> maps a real parameter to the corresponding point on the line. The colon specifies the input type.</p>
<p><code>f ∘ line</code> is function composition: it maps <code>t</code> to <code>f (line t)</code>. The circle is not multiplication. A bundled affine map or an element of <code>Lp</code> can appear where a function is expected because Lean has a conversion, called a <em>coercion</em>, to its underlying function or chosen representative. The notes explain when such a conversion is being used.</p>
</details>

<details class="guide-topic" id="lean-dot">
<summary>Qualified names, theorem application, and component selection</summary>
<p>A dot can separate parts of a name. <code>AffineMap.lineMap</code> is the construction <code>lineMap</code> inside the namespace <code>AffineMap</code>. A namespace organizes library declarations and helps distinguish similarly named things. Names are case-sensitive: the initial capital <code>A</code> and <code>M</code> matter. <code>affineMap.lineMap</code> is not the same identifier.</p>
<p>A dot can also be <em>generalized field notation</em>: a convenient way to pass an object or proof to a suitable theorem. In this proof, <code>hf.comp_affineMap line</code> is the theorem application <code>ConvexOn.comp_affineMap line hf</code>. Lean uses the type of <code>hf</code> to find the theorem and inserts <code>hf</code> into the appropriate argument position. It does not always insert the object as the first explicit argument; the theorem’s declaration determines the placement.</p>
<p>In <code>hxy.trans hyz</code>, <code>.trans</code> combines compatible equalities or inequalities by transitivity. For example, a proof of <code>a ≤ b</code> and a proof of <code>b ≤ c</code> yield a proof of <code>a ≤ c</code>. The local notes state the intermediate expressions when this occurs.</p>
<p>A dot may instead select a structure field or a component. <code>ref.segment</code> selects the segment field from a reference structure. <code>ht.1</code> and <code>ht.2</code> select the first and second components of a pair of facts, such as the two inequalities in interval membership. Which use is intended depends on the type of the expression before the dot. It is not decimal notation or multiplication.</p>
</details>

<details class="guide-topic" id="lean-affine-map">
<summary>Affine maps and parameterized lines</summary>
<p>The full notation <code>A →ᵃ[k] B</code> names the type <code>AffineMap k A B</code>: affine maps from <code>A</code> to <code>B</code> over the scalar system <code>k</code>. The superscript <code>ᵃ</code> is a marker for affine maps. It is not a variable exponent, and this is not an ordinary function arrow followed by an extra hypothesis.</p>
<p>Thus <code>ℝ →ᵃ[ℝ] H</code> has three pieces: input space <code>ℝ</code>, scalar system <code>ℝ</code> inside the brackets, and output space <code>H</code>. An affine map includes both its underlying function and the algebraic structure witnessing affinity. In this setting an affine map preserves affine combinations. Such a map can be evaluated like a function, so <code>line t</code> is meaningful.</p>
<p><code>AffineMap.lineMap</code> is a construction already proved valid in mathlib. Given two points <code>x y : H</code>, <code>AffineMap.lineMap x y</code> is the parameterized line:</p>
\[\operatorname{line}(t)=t(y-x)+x=(1-t)x+ty.\]
<p>At <code>t = 0</code> it returns <code>x</code>; at <code>t = 1</code> it returns <code>y</code>. The domain is every real parameter, not just the interval from zero to one. Supplying <code>x</code> and <code>y</code> constructs the whole map; supplying another argument <code>t</code> evaluates it. If <code>x = y</code>, the map is constant, which is still affine.</p>
<p>The Lean expression <code>t • (y - x) + x</code> uses <code>•</code> for scalar multiplication of a vector. It differs from <code>*</code>, which is multiplication in a type with a multiplication operation. The construction works in more general affine spaces too; the formula above is its specialized form for a vector space such as this <code>H</code>.</p>
<p><strong>How to write the type without the decorated arrow:</strong> use <code>AffineMap ℝ ℝ H</code>. This names exactly the same type. To enter the decorated arrow with the Lean VS Code extension, see <a href="#lean-unicode">the keystrokes below</a>.</p>
</details>

<details class="guide-topic" id="lean-simp">
<summary>Simplification and expansion of definitions with <code>simp</code></summary>
<p><code>simp</code> is the simplifier tactic. It uses definitions you explicitly ask it to unfold and a collection of proven simplification rules, for example that adding zero changes nothing. Each replacement is justified; it does not decide arbitrary mathematical questions by guessing.</p>
<p>After <code>simp</code>, square brackets supply additional instructions for this simplification. In <code>simp [line]</code>, <code>line</code> is a local definition, so the list tells the simplifier it may unfold <code>line</code> to its defining value. The fact that it was introduced by <code>let</code> is exactly what makes that value available.</p>
<p>If a list entry is instead an equality lemma, the simplifier can use that equality as a rewrite rule. Thus <code>simp [line, someEquality]</code> may contain both a definition to unfold and a theorem to rewrite with. These brackets are tactic syntax. They are not declaring a typeclass instance, constructing a vector containing <code>line</code>, or evaluating <code>line</code> at an input.</p>
<p><code>simp only [a, b]</code> restricts the selected theorem/definition rules to the listed entries, while retaining built-in reduction behavior. Ordinary <code>simp [a, b]</code> also uses the usual simplification collection. <code>simp […] at hs</code> simplifies a named hypothesis <code>hs</code>; without <code>at</code>, it normally simplifies the target. <code>at hs ⊢</code> requests both the hypothesis and the goal.</p>
<p>A useful distinction: <code>simp</code> may completely prove the target, or it may leave a simpler target requiring more work. <code>dsimp</code> focuses on definitional simplification. <code>simp_rw</code> repeatedly uses the specified rewrites and can rewrite under binders. The exact instructions matter, so each appearance has a local explanation.</p>
</details>

<details class="guide-topic" id="lean-simpa">
<summary>Simplification of a supplied proof with <code>simpa</code></summary>
<p><code>simpa</code> asks Lean to finish the current goal by simplification. The form <code>simpa using h</code> supplies an existing proof <code>h</code>, simplifies its statement and the target as needed, and succeeds when the resulting statements match. If they do not match, the command fails; it does not simply move on with an unproved result.</p>
<p>Break the actual command into its parts:</p>
<dl class="syntax-parts"><dt><code>simpa</code></dt><dd>Close the current goal through simplification.</dd><dt><code>[line]</code></dt><dd>Add the local definition <code>line</code> to the things that can be unfolded.</dd><dt><code>using</code></dt><dd>The expression that follows is an existing proof to adapt to the target.</dd><dt><code>hf.comp_affineMap line</code></dt><dd>Apply the convexity-under-affine-composition theorem to the given convexity proof <code>hf</code> and affine map <code>line</code>.</dd></dl>
<p>The library theorem initially gives convexity on the inverse image of the original set:</p>
<pre class="note-code">ConvexOn ℝ (line ⁻¹' Set.univ) (f ∘ line)</pre>
<p>The goal asks for:</p>
<pre class="note-code">ConvexOn ℝ Set.univ (f ∘ line)</pre>
<p>The inverse image of the entire output space under any function is the entire input space: <code>line ⁻¹' Set.univ = Set.univ</code>. Simplification removes that harmless difference. The list <code>[line]</code> also allows the local name to be unfolded; it does not mean “assume the convexity result” and does not itself establish convexity. That mathematical content comes from <code>hf.comp_affineMap line</code>.</p>
<p>In the surrounding code, the current goal belongs to <code>have hc … := by</code>. Finishing it creates <code>hc</code>, the convexity proof for the restricted function. The outer supporting-plane theorem is still being proved after that subproof closes.</p>
</details>

<details class="guide-topic" id="lean-binders">
<summary>Parentheses, braces, square brackets, named arguments, and <code>_</code></summary>
<p><code>(x : H)</code> declares an explicit parameter: when applying the declaration, you normally supply its value. <code>{x : H}</code> declares an implicit parameter: Lean normally infers it from other arguments or from the expected result. Curly braces do not mean that the hypothesis is optional mathematically; its value must still be determined.</p>
<p><code>[CompleteSpace H]</code> requests a typeclass instance. Such an instance supplies a specified structure or property—in this case completeness of the space <code>H</code>. <code>[InnerProductSpace ℝ H]</code> supplies its real inner-product-space structure. Typeclass search finds these instances from the context. The square brackets here belong to a parameter declaration and have a different purpose from the brackets in <code>simp [line]</code>.</p>
<p><code>(hf : ConvexOn ℝ Set.univ f)</code> is an explicit hypothesis parameter, whose value is a proof of convexity. <code>(x y : H)</code> declares two parameters with the same type. A local variable declaration such as <code>variable {H : Type*} …</code> supplies parameters reused by the declarations that follow; relevant ones are added to those declarations automatically.</p>
<p><code>(μ := P)</code> is a named argument: it says to use <code>P</code> for the parameter whose name is <code>μ</code>. It is unrelated to a new local <code>let</code> assignment. A standalone <code>_</code> is a placeholder asking Lean to infer an expression. In <code>refine someTheorem ?_</code>, <code>?_</code> deliberately leaves an obligation to prove as a new goal. Neither form means that you may leave a proof permanently incomplete.</p>
<p>Inside a <code>calc</code> chain, an underscore on the left continues the previous line’s right-hand expression. In patterns such as <code>fun _ ↦ value</code>, it indicates an input name that will not be used. Context tells these different uses apart.</p>
</details>

<details class="guide-topic" id="lean-proof-terms">
<summary>Proof terms, <code>exact</code>, <code>rfl</code>, and <code>show</code></summary>
<p>A <em>proof term</em> is an expression that Lean checks has the target proposition as its type. If <code>h : P</code> is already available and the goal is <code>P</code>, the tactic <code>exact h</code> supplies that proof and closes the goal. A theorem applied to suitable arguments is itself a proof term for the resulting conclusion.</p>
<p><code>exact</code> is a tactic; the expression after it need not be a tactic. For example, <code>exact hc.trans hbound</code> supplies the proof term formed by transitivity. A parenthesized <code>(by …)</code> embedded among theorem arguments builds a proof of the expected hypothesis in place, rather than first naming it with <code>have</code>.</p>
<p><code>rfl</code> proves equality when both sides are definitionally equal—when they compute or unfold to the same expression with the appropriate reductions. The zero and successor recursion equations often have this form. It is not a general tactic for proving any true equality. It can appear as <code>:= rfl</code> in a declaration or as the tactic <code>rfl</code> inside <code>by</code>.</p>
<p><code>show T from expression</code> explicitly states the type expected of an expression. The tactic form <code>show T</code> changes the displayed target to a definitionally equal presentation. Similarly, <code>change T</code> asks Lean to view the current target as a definitionally equal expression. These commands do not allow replacing the target by an arbitrary easier statement.</p>
</details>

<details class="guide-topic" id="lean-rewrite">
<summary>Rewriting and successive equalities or inequalities</summary>
<p><code>rw [h]</code> uses an equality or suitable equivalence <code>h</code> to replace one expression by another in the target. If <code>h</code> proves <code>a = b</code>, the usual direction replaces <code>a</code> by <code>b</code>. <code>rw [← h]</code> reverses that direction. The arrow is an instruction about rewriting, not a new implication or a modification of the theorem.</p>
<p><code>rw [h] at hs</code> rewrites the hypothesis named <code>hs</code>. A list such as <code>rw [h1, h2]</code> performs the rewrites in order, so the second sees the expression produced by the first. Some rewriting commands can finish the goal when the resulting equality is reflexive; otherwise there is a remaining target.</p>
<p><code>rwa</code> rewrites and then tries to close by an available matching assumption. <code>simp only […] at hxy ⊢</code> is simplification at both a fact and the target. Read the <code>at</code> part carefully: it tells you which statement is being transformed.</p>
<p><code>calc</code> introduces a chain of equalities or inequalities, with a proof after each <code>:=</code>:</p>
<pre class="note-code">calc
  a ≤ b := hab
  _ ≤ c := hbc</pre>
<p>The underscore stands for <code>b</code>, the previous right-hand side. The entire chain produces a proof of <code>a ≤ c</code>. Rewrites, transitivity, and inequality bounds in this document follow exactly the same mathematical equalities as the corresponding prose.</p>
</details>

<details class="guide-topic" id="lean-tactics">
<summary>Other recurring tactics: arithmetic, application, cases, and induction</summary>
<p><code>apply theoremName</code> works backward: it matches the theorem’s conclusion to the goal and leaves any required premises that Lean cannot infer as new goals. <code>refine</code> lets you supply a partially specified proof term with explicit holes. <code>intro</code> introduces an arbitrary variable or an implication’s hypothesis when proving a universally quantified or conditional statement.</p>
<p><code>linarith</code> combines available linear arithmetic relations. <code>nlinarith</code> also preprocesses polynomial expressions for certain nonlinear consequences. They produce checked proofs, but they do not solve all true real inequalities. Expressions involving norms, roots, or integrals often first need explicit lemmas to put the problem into a form the tactic can use. Supplying <code>nlinarith [h1, h2]</code> adds those facts to the arithmetic inputs.</p>
<p><code>ring</code> proves a polynomial identity by normalization in a suitable commutative algebraic structure; it does not prove an arbitrary inequality. <code>module</code> normalizes vector-space or module expressions. <code>abel</code> normalizes additive commutative-group expressions. <code>field_simp</code> clears denominators and may leave nonzero-denominator obligations. <code>norm_num</code> handles explicit numerical arithmetic. <code>positivity</code> tries to establish sign facts from the expression and known signs. <code>fun_prop</code> composes recognized function-property lemmas, such as continuity.</p>
<p><code>by_cases h : P</code> splits into a branch with <code>h : P</code> and another with <code>h : ¬ P</code>. <code>induction n with</code> proves a natural-number statement in a zero case and a successor case; the latter receives an induction hypothesis, often named <code>ih</code>. <code>rcases</code> or <code>obtain</code> unpack witnesses and facts from an existing proof. <code>constructor</code> starts proving the fields of a structure or the components of a conjunction. The local notes identify exactly what these branches and fields are in the current proof.</p>
</details>

<details class="guide-topic" id="lean-structures">
<summary>Structures, <code>where</code>, field access, namespaces, and imports</summary>
<p><code>structure … where</code> defines a type of records with named fields. Some fields are mathematical data; others are proofs that the data satisfy required properties. For example, a coupling contains a joint measure and proofs identifying its marginals. Constructing a coupling means supplying every required field.</p>
<p>In a record construction, <code>joint := expression</code> supplies a field’s value. <code>fst := by …</code> supplies a proof for another field. In <code>ref.segment</code>, a dot retrieves a field from the particular structure value <code>ref</code>. Merely declaring the structure <code>L2Reference</code> does not construct a Langevin reference. A theorem parameter <code>(ref : L2Reference …)</code> requires the caller to supply a reference with all its proof fields.</p>
<p><code>import Module.Name</code> loads declarations from another checked module. <code>namespace ULA</code> places subsequent names under that prefix until the matching <code>end ULA</code>. <code>open MeasureTheory</code> allows eligible names from that namespace to be used without repeatedly writing the prefix. <code>open scoped NNReal</code> enables notation in that scope. These are setup instructions; they are not additional mathematical assumptions.</p>
<p><code>noncomputable section</code> permits definitions relying on noncomputable choices, such as certain analytic constructions. It does not permit unproved statements. <code>@[simp]</code> registers a suitable theorem as a simplification rule. <code>omit [SomeInstance H] in</code> can prevent an unused surrounding instance from being included in the next declaration’s parameters. Comments start with <code>--</code> or are enclosed by <code>/- … -/</code>; documentation comments use <code>/-- … -/</code>. Comments explain the source to humans and are not proof steps.</p>
</details>

<details class="guide-topic" id="lean-probability">
<summary>Probability notation: <code>P.map</code>, <code>∀ᵐ</code>, <code>MemLp</code>, <code>Lp</code>, and <code>toReal</code></summary>
<p><code>P : Measure Ω</code> is a measure on the outcome space <code>Ω</code>. An instance <code>[IsProbabilityMeasure P]</code> asserts that its total mass is one. <code>P.map X</code> is the pushforward measure, hence the law of the random variable <code>X</code> when measurability is available. It is not a pointwise evaluation of a distribution.</p>
<p><code>∀ᵐ ω ∂P, Q ω</code> means that <code>Q</code> holds for almost every outcome with respect to <code>P</code>, allowing an exceptional set of measure zero. <code>F =ᵐ[P] G</code> means almost-everywhere equality. A statement of that form is weaker than equality at every outcome. The tactic <code>filter_upwards</code> combines finitely many such almost-everywhere facts and reduces the proof to ordinary reasoning on a common full-measure set.</p>
<p><code>MemLp X 2 P</code> packages almost-everywhere strong measurability and a finite second-power norm. <code>Lp H 2 P</code> is a type of square-integrable equivalence classes: functions that agree almost everywhere represent the same element. The norm of such an element is a finite real number. Using an <code>Lp</code> element as a function chooses a representative; identities between representatives frequently hold only almost everywhere.</p>
<p><code>ℝ≥0∞</code> includes infinity, while <code>ℝ≥0</code> contains only finite nonnegative real numbers. The transport cost and its infimum are initially defined with values in <code>ℝ≥0∞</code>. Conversion by <code>.toReal</code> is not an order-preserving replacement for infinity: Lean’s definition gives <code>(∞ : ℝ≥0∞).toReal = 0</code>. Thus a bound on the converted value alone would tell you nothing about whether the original value was finite. Finite-upper-bound hypotheses are needed before converting these inequalities. The notes spell out those finiteness arguments instead of silently interpreting every extended quantity as an ordinary distance.</p>
</details>

<details class="guide-topic" id="lean-integrals">
<summary>Integrals, derivative assertions, continuity, and norm notation</summary>
<p><code>∫ t in 0..h, expression</code> is an interval integral with variable <code>t</code>, from zero to <code>h</code>. In these modules it is a Bochner integral, which can integrate vector-valued functions. <code>IntervalIntegrable F volume 0 h</code> is the hypothesis needed for many interval-integral identities. The presence of an integral expression alone does not assert integrability.</p>
<p><code>HasDerivAt F v t</code> asserts that a real-parameter function <code>F</code> has derivative <code>v</code> at parameter <code>t</code>. The value <code>v</code> can be a vector. <code>HasFDerivAt f A x</code> asserts that the multivariable derivative of <code>f</code> at <code>x</code> is the continuous linear map <code>A</code>. <code>Differentiable ℝ f</code> asserts differentiability at every point over real scalars. The notes distinguish these assertions from the derivative-valued functions <code>fderiv</code> and <code>gradient</code>.</p>
<p><code>‖v‖</code> is the norm in the type of <code>v</code>. In <code>Lp … 2 P</code> it is the \(L^2\) norm, whereas in <code>H</code> it is the ambient norm. <code>inner ℝ u v</code> is the real inner product. <code>Real.sqrt a</code> is the real square-root function; lemmas about its square require appropriate sign conditions. <code>(L : ℝ)</code> explicitly converts a nonnegative-real parameter to an ordinary real number.</p>
<p><code>Set.Icc 0 h</code> is the closed interval. A proof <code>ht : t ∈ Set.Icc 0 h</code> includes the two facts <code>0 ≤ t</code> and <code>t ≤ h</code>, obtained as <code>ht.1</code> and <code>ht.2</code>. <code>Continuous Y</code>, <code>Measurable X</code>, and <code>AEMeasurable X P</code> express different function properties; the latter permits changing values on a null set. They are used only where the respective library theorem calls for them.</p>
</details>

<details class="guide-topic" id="lean-unicode">
<summary>Keyboard entry of mathematical symbols</summary>
<p>In a <code>.lean</code> file with the Lean 4 extension active in VS Code, type a backslash, then an abbreviation, then <kbd>Tab</kbd> to accept the symbol. These input abbreviations are an editor feature; the saved Lean source contains the resulting Unicode characters. They do not turn into symbols when typed in an ordinary browser text box.</p>
<p><strong>To enter <code>ℝ →ᵃ[ℝ] H</code>:</strong> type <code>\R</code>, press <kbd>Tab</kbd>, then a space; type <code>\r</code>, press <kbd>Tab</kbd>; type <code>\^a</code>, press <kbd>Tab</kbd>; type <code>[</code>; type <code>\R</code>, press <kbd>Tab</kbd>; type <code>]</code>, then a space and <code>H</code>. The superscript <code>ᵃ</code> is a separate Unicode character. The literal source text <code>-&gt;^a</code> does not spell the decorated affine-map notation.</p>
<p>You may instead copy <code>ℝ →ᵃ[ℝ] H</code>, or write <code>AffineMap ℝ ℝ H</code> and avoid the decorated arrow entirely. Ordinary function arrows can use the ASCII spelling <code>-&gt;</code>. Ordinary lambda arrows can use <code>=&gt;</code>.</p>
<table class="typing-table"><thead><tr><th>Symbol in source</th><th>Type, then Tab</th><th>Meaning here</th></tr></thead><tbody>
<tr><td><code>→</code></td><td><code>\r</code> or <code>\to</code></td><td>Function arrow; logical implication between propositions</td></tr>
<tr><td><code>ᵃ</code></td><td><code>\^a</code></td><td>Superscript a in the affine-map notation</td></tr>
<tr><td><code>ℝ</code>, <code>ℕ</code></td><td><code>\R</code>, <code>\N</code></td><td>Real numbers, natural numbers</td></tr>
<tr><td><code>ℝ≥0</code>, <code>ℝ≥0∞</code></td><td><code>\nnreal</code>, <code>\ennreal</code></td><td>Nonnegative reals, extended nonnegative reals</td></tr>
<tr><td><code>↦</code></td><td><code>\mapsto</code></td><td>Lambda arrow after <code>fun</code>; ASCII <code>=&gt;</code> also works</td></tr>
<tr><td><code>∘</code></td><td><code>\circ</code> or <code>\o</code></td><td>Function composition</td></tr>
<tr><td><code>•</code></td><td><code>\smul</code></td><td>Scalar multiplication</td></tr>
<tr><td><code>∀</code>, <code>∃</code></td><td><code>\forall</code>, <code>\exists</code></td><td>For every, there exists</td></tr>
<tr><td><code>∀ᵐ</code>, <code>=ᵐ</code></td><td>Enter <code>∀</code> or <code>=</code>, then <code>\^m</code></td><td>Almost-everywhere quantifier or equality</td></tr>
<tr><td><code>≤</code>, <code>≥</code>, <code>≠</code></td><td><code>\le</code>, <code>\ge</code>, <code>\ne</code></td><td>Order and inequality</td></tr>
<tr><td><code>←</code></td><td><code>\l</code></td><td>Reverse direction in a rewrite rule</td></tr>
<tr><td><code>⊢</code></td><td><code>\vdash</code></td><td>Marks the goal in a proof-state display</td></tr>
<tr><td><code>∈</code>, <code>∧</code>, <code>↔</code></td><td><code>\in</code>, <code>\and</code>, <code>\iff</code></td><td>Membership, conjunction, equivalence</td></tr>
<tr><td><code>⟨</code>, <code>⟩</code></td><td><code>\langle</code>, <code>\rangle</code></td><td>Package witnesses or proof components</td></tr>
<tr><td><code>‖</code></td><td><code>\||</code></td><td>One norm delimiter; enter one on each side</td></tr>
<tr><td><code>∫</code></td><td><code>\integral</code></td><td>Integral; <code>\int</code> instead gives the integer type <code>ℤ</code></td></tr>
<tr><td><code>∞</code>, <code>⨅</code>, <code>𝓝</code></td><td><code>\infty</code>, <code>\infi</code>, <code>\nhds</code></td><td>Infinity, indexed infimum, neighborhood filter</td></tr>
<tr><td><code>⊤</code>, <code>∑</code>, <code>×</code></td><td><code>\top</code>, <code>\sum</code>, <code>\times</code></td><td>Greatest element, finite sum, product type</td></tr>
<tr><td><code>∂</code></td><td><code>\partial</code></td><td>Introduces the integration measure in these integral expressions</td></tr>
<tr><td><code>μ</code>, <code>ν</code>, <code>π</code></td><td><code>\mu</code>, <code>\nu</code>, <code>\pi</code></td><td>Greek variable names for measures in this development</td></tr>
<tr><td><code>Ω</code>, <code>ω</code></td><td><code>\Omega</code>, <code>\omega</code></td><td>Greek variable names for an outcome space and an outcome</td></tr>
<tr><td><code>γ</code>, <code>ε</code></td><td><code>\gamma</code>, <code>\epsilon</code></td><td>Greek variable names used for a coupling measure or accuracy parameter</td></tr>
<tr><td><code>₀</code>, <code>₁</code>, <code>₂</code></td><td><code>\_0</code>, <code>\_1</code>, <code>\_2</code></td><td>Subscript characters used in names, distinct from an indexing expression</td></tr>
</tbody></table>
<p>The two characters in <code>:=</code>, the colon <code>:</code>, square brackets, parentheses, and commas are typed normally. A subscript or superscript in an identifier is often only part of that identifier’s spelling: <code>p₀</code> and <code>p₁</code> are names. In contrast, <code>q ^ n</code> is an exponentiation expression. Hovering over Unicode symbols in the Lean editor can show their input abbreviations.</p>
<p>These abbreviations were checked against the installed Lean extension’s table. The extension’s <a href="https://github.com/leanprover/vscode-lean4/blob/master/lean4-unicode-input/src/abbreviations.json">official abbreviation table</a> is a reference for additional symbols. To inspect a library declaration in VS Code, hover over its name or use Go to Definition; this is how to see the precise hypotheses of <code>AffineMap.lineMap</code> or a theorem called by dot notation.</p>
</details>
<details class="guide-topic" id="lean-library-tools">
<summary>Looking up library declarations</summary>
<p>Names such as <code>comp_hasDerivAt_of_eq</code> are library declarations, not new language keywords. You do not have to infer their complete meaning from their spelling. In the Lean editor, hover over the name to see its type, and use Go to Definition to inspect its declaration and documentation. A theorem’s type tells you its inputs and the result it produces. Dots, underscores, and capitalization are part of the name; underscores inside <code>hasDerivAt_id</code> are not holes.</p>
<p>In a scratch Lean file with the necessary imports, <code>#check AffineMap.lineMap</code> asks Lean to print the type of the construction. <code>#print AffineMap.lineMap</code> also prints its defining body. These are commands for inspecting declarations, rather than tactics to insert into an unfinished proof. A long library declaration often has implicit type and instance parameters before the explicit mathematical arguments; that is why the displayed type may be longer than the short use in this document.</p>
<p>The appendix’s <code>#print axioms theoremName</code> commands inspect which logical axioms a theorem ultimately depends on. They do not add those axioms or prove the theorem. This project’s audit reports Lean’s standard logical dependencies. A theorem with a supplied hypothesis remains conditional on that hypothesis, regardless of its axiom report. The proof of a reference-process existence theorem cannot be replaced by a structure declaration or by an axiom audit.</p>
<p>The local Lean notes explain the particular library facts used in each line. When you begin experimenting in the editor, copy the relevant module’s imports and ambient variable declarations as well as the theorem body, or work directly in a scratch file importing that module. A declaration excerpt may use names and instances introduced earlier in its module.</p>
</details>
<p class="guide-reference">For further reading, Lean’s <a href="https://lean-lang.org/theorem_proving_in_lean4/Tactics/">introduction to tactic proofs</a> and <a href="https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/">tactic reference</a> describe the general commands. The notes in this document explain their uses in the repository’s pinned Lean version.</p>
</div>
</details>
