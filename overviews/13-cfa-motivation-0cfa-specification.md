---
title: Control Flow Analysis — Motivation & the 0-CFA Specification
abbrev: CFA (0-CFA spec)
lectures: "17 (CFA), master deck: CFA-for-FUN"
paper: "Nielson, Nielson & Hankin, Principles of Program Analysis, Ch. 3; Shivers (Scheme CFA)"
theme: "which functions can flow to which call sites — the Flow Logic acceptability specification"
oneliner: "0-CFA over-approximates, for every call site, the set of functions it may invoke, specified by an acceptability relation (Ĉ,ρ̂) ⊧ e."
render: "Notation is LaTeX math ($…$ / $$…$$). Preview with a KaTeX markdown extension."
---

# Control Flow Analysis — Motivation & the 0-CFA Specification

**Theme:** the first CFA topic. In a higher-order language you cannot read the call graph
off the syntax — a call `f x` invokes *whatever function `f` happens to hold*. CFA computes
a safe over-approximation of that. This file sets up the problem and gives the **Flow Logic**
specification of **0-CFA**; correctness, least solutions, and solving come in files 14–16.

## 1. Purpose & core idea
In first-order code the control-flow graph is explicit. With **higher-order functions**
(functions passed/returned/stored) the target of a call is a *runtime value* — the **dynamic
dispatch problem**. E.g. in `(f g) + (f h)`, which function does `f`'s parameter get applied
to? **Control Flow Analysis** answers, for **each call site, a sound over-approximation of the
set of functions it may call** — recovering an (approximate) call graph so that other analyses
and optimisations become possible. **0-CFA** is the simplest form: **context-insensitive**
(one answer per program point, the same at all calls).

## 2. Setup — the language FUN, labelling, and the abstract domains
**FUN** (labelled λ-calculus with recursion, conditionals, `let`, binary ops):
$$t ::= c \mid x \mid \mathsf{fn}\ x\Rightarrow e_0 \mid \mathsf{fun}\ f\ x\Rightarrow e_0 \mid e_1\,e_2 \mid \mathsf{if}\ e_0\ e_1\ e_2 \mid \mathsf{let}\ x=e_1\ \mathsf{in}\ e_2 \mid e_1\ \mathsf{op}\ e_2, \qquad e ::= t^l.$$
Every subterm carries a distinct **label** $l\in\mathit{Lab}$ marking a **program point** (in
particular each call site). The analysis result is a pair $(\hat C,\hat\rho)$:

$$\hat C\in\widehat{\mathit{Cache}}:\mathit{Lab}\to\widehat{\mathit{Val}},\qquad \hat\rho\in\widehat{\mathit{Env}}:\mathit{Var}\to\widehat{\mathit{Val}},\qquad \hat v\in\widehat{\mathit{Val}}=\wp(\mathit{Term}).$$

- an **abstract value** is a **set of function abstractions** ($\mathsf{fn}/\mathsf{fun}$ terms);
- the **abstract cache** $\hat C(l)$ = functions the subterm at $l$ **may evaluate to**;
- the **abstract environment** $\hat\rho(x)$ = functions **variable $x$ may be bound to**.

(*Pure* CFA tracks only functions, no data values — "0" also flags no context; combining with
data-flow comes in [17](17-beyond-0cfa-abstract-values-context.md).)

## 3. The specification — the acceptability relation $(\hat C,\hat\rho)\models e$
CFA is given in **Flow Logic** style: rather than *compute* a solution, we **specify what a
correct solution is** and *validate a guess*. A guess $(\hat C,\hat\rho)$ is **acceptable** for
$e$, written $(\hat C,\hat\rho)\models e$, iff it **safely over-approximates** every runtime
flow — one clause per syntactic form (each an inclusion the guess must satisfy):

> [!important] The 0-CFA clauses
> $$[\textsf{con}]\quad (\hat C,\hat\rho)\models c^l \iff \text{true}\quad(\text{constants aren't functions: no demand on }\hat C(l))$$
> $$[\textsf{var}]\quad (\hat C,\hat\rho)\models x^l \iff \hat\rho(x)\subseteq\hat C(l)\quad(\text{flow variable} \to \text{program point})$$
> $$[\textsf{fn}]\quad (\hat C,\hat\rho)\models (\mathsf{fn}\ x\Rightarrow e_0)^l \iff \{\mathsf{fn}\ x\Rightarrow e_0\}\subseteq\hat C(l)\qquad [\textsf{fun}]\ \text{likewise records the recursive closure}$$
> $$[\textsf{if}]\quad (\hat C,\hat\rho)\models(\mathsf{if}\ t_0^{l_0}\ t_1^{l_1}\ t_2^{l_2})^l \iff (\hat C,\hat\rho)\models t_0^{l_0}\wedge\bigwedge_{i=1,2}\big((\hat C,\hat\rho)\models t_i^{l_i}\wedge \hat C(l_i)\subseteq\hat C(l)\big)$$
> $$[\textsf{let}]\quad (\hat C,\hat\rho)\models(\mathsf{let}\ x{=}t_1^{l_1}\ \mathsf{in}\ t_2^{l_2})^l \iff (\hat C,\hat\rho)\models t_1^{l_1}\wedge(\hat C,\hat\rho)\models t_2^{l_2}\wedge \underbrace{\hat C(l_1)\subseteq\hat\rho(x)}_{\text{bind}}\wedge\underbrace{\hat C(l_2)\subseteq\hat C(l)}_{\text{result}}$$
> $$[\textsf{app}]\quad (\hat C,\hat\rho)\models(t_1^{l_1}\,t_2^{l_2})^l \iff (\hat C,\hat\rho)\models t_1^{l_1}\wedge(\hat C,\hat\rho)\models t_2^{l_2}\ \wedge$$
> $$\forall(\mathsf{fn}\ x\Rightarrow t_0^{l_0})\in\hat C(l_1):\ (\hat C,\hat\rho)\models t_0^{l_0}\ \wedge\ \underbrace{\hat C(l_2)\subseteq\hat\rho(x)}_{\text{arg}\to\text{param}}\ \wedge\ \underbrace{\hat C(l_0)\subseteq\hat C(l)}_{\text{body}\to\text{call site}}\quad(\text{and analogously for }\mathsf{fun}).$$
> $$[\textsf{op}]\quad (\hat C,\hat\rho)\models(t_1^{l_1}\,\mathsf{op}\,t_2^{l_2})^l \iff (\hat C,\hat\rho)\models t_1^{l_1}\wedge(\hat C,\hat\rho)\models t_2^{l_2}\quad(\text{result is a base value: no demand on }\hat C(l),\ \text{like }[\textsf{con}])$$

The whole idea lives in **[app]**: for **every** function $t_1$ might be, push the argument into
its parameter and its body's result back to the call site. That single clause is what threads
values through higher-order calls.

### 3a. Reading each clause intuitively — the plumbing picture
**One mental model for all of it.** Picture two kinds of **buckets**, each holding a *set of
functions*: a bucket $\hat C(l)$ for every program point $l$ ("what value comes out **here**")
and a bucket $\hat\rho(x)$ for every variable $x$ ("what $x$ **holds**"). Every clause is just a
**pipe** written as an inclusion `⊆`: *"everything in the left bucket must also be in the right
bucket."* A guess is **acceptable** iff **all the pipes are installed** so no function can ever
flow somewhere without being recorded there. Functions are **poured in** only by `[fn]/[fun]`;
every other rule just **routes** them. `⊆` (not `=`) is what makes it an *over*-approximation:
buckets are allowed to hold *extra* junk, they just may not **miss** anything real.

- **[con] $c^l$ — nothing to track.** A constant evaluates to a *number*, never a function. Since
  buckets only ever hold functions, there is nothing to pour into $\hat C(l)$, so the clause is
  just `true` — no pipe, the bucket may stay empty. (Any guess is acceptable for a constant.)

- **[var] $x^l$ — read the variable.** Evaluating $x$ yields whatever $x$ is currently bound to.
  So whatever sits in $x$'s bucket must appear at this point: **$\hat\rho(x)\subseteq\hat C(l)$**.
  One pipe, *variable-bucket → point-bucket*. This is where a stored function gets **read back
  out** into the flow.

- **[fn]/[fun] $(\mathsf{fn}\ x\Rightarrow e_0)^l$ — the only source.** A function *literal*
  evaluates **to itself** (its closure). So the term itself must be dropped into this point's
  bucket: **$\{\mathsf{fn}\ x\Rightarrow e_0\}\subseteq\hat C(l)$**. This is the **only** rule that
  *introduces* a function into the analysis — every function in every bucket anywhere was
  ultimately poured in here and then routed by the other rules. `[fun]` is identical but the
  closure also carries its own recursive name $f$.

- **[if] $\mathsf{if}\ t_0\ t_1\ t_2$ — merge both branches.** First the guard $t_0$ must itself
  be acceptable (it may contain calls). The result of the `if` is the value of *whichever* branch
  runs — but 0-CFA **can't tell which**, so it conservatively assumes **either** could, and pipes
  **both** branch buckets into the result: **$\hat C(l_1)\subseteq\hat C(l)$ and
  $\hat C(l_2)\subseteq\hat C(l)$**. (No pipe *from* the guard's value — a boolean isn't a
  function.) Forgetting which branch is taken is exactly the imprecision you pay for decidability.

- **[let] $\mathsf{let}\ x=t_1\ \mathsf{in}\ t_2$ — bind, then return.** Two pipes. **bind:** the
  definition's value becomes $x$'s binding, **$\hat C(l_1)\subseteq\hat\rho(x)$** (fill $x$'s
  bucket from $t_1$). **result:** the whole `let` returns the body's value,
  **$\hat C(l_2)\subseteq\hat C(l)$**. Plus both sub-terms must be acceptable. It's `[var]` and
  `[app]`'s binding logic in miniature: *definition → variable → (used later by `[var]`) → body.*

- **[app] $t_1\ t_2$ — the heart, dynamic dispatch.** $t_1$ is the *function position*, $t_2$ the
  *argument*. The bucket $\hat C(l_1)$ **is the analysis's answer** to "which functions might be
  called here." For **each** candidate $\mathsf{fn}\ x\Rightarrow t_0^{l_0}$ found in that bucket,
  install three things: (i) its **body is reached**, so $t_0^{l_0}$ must itself be acceptable;
  (ii) **arg → param:** the argument flows into that function's parameter,
  **$\hat C(l_2)\subseteq\hat\rho(x)$**; (iii) **body → call site:** the function's result flows
  back out to this call, **$\hat C(l_0)\subseteq\hat C(l)$**. The subtlety: *which* functions you
  quantify over is **not known from the syntax** — it depends on $\hat C(l_1)$, which the analysis
  is itself computing. That self-reference ("the constraints depend on the current guess") is the
  **coinductive/greatest-fixpoint** flavour noted in §4, and the reason CFA is more than a simple
  syntactic walk.

- **[op] $t_1\ \mathsf{op}\ t_2$ — like [con].** Arithmetic/comparison returns a *base value*, not
  a function, so **no demand on $\hat C(l)$**. But unlike a bare constant, the operands are
  arbitrary expressions that might build or call functions internally, so **both must be
  acceptable** ($\models t_1\wedge\models t_2$) even though their result-buckets are ignored.

**The through-line:** `[fn]/[fun]` are the *taps*, `[var]`/`[let]`/`[app]` are the *pipes* that
carry functions from where they're created to where they're stored, read, and called, and
`[con]`/`[op]` are *dead ends* (base values). "Acceptable" = you laid down enough pipe that the
water level in every bucket is a safe over-estimate of what really flows there at runtime.

## 4. Properties — what "acceptable" means
- **Soundness = over-approximation.** If at runtime $t^l$ evaluates to a function, that function
  is recorded in $\hat C(l)$ (and bindings in $\hat\rho$). A **conservative (over-approximating)
  guess is acceptable; an incomplete one (a false negative) is not.** So `⊧` accepts exactly the
  *safe* guesses. Formal correctness (subject reduction) is [file 14](14-0cfa-semantic-correctness.md).
- **Specification, not algorithm.** The clauses *validate* a guess; they don't compute one. That
  many guesses are acceptable (the full $\top$ is always acceptable) raises the question of the
  **least/best** one → [file 15](15-0cfa-existence-least-solutions.md); *computing* it → [file 16](16-0cfa-constraint-based-solving.md).
- **Coinductive flavour.** Because `[app]` refers to the body of functions that may reach $l_1$
  (themselves determined by the analysis), acceptability is defined by a **greatest fixpoint /
  coinductive** reading (the least *solution* is then extracted separately).
- **0-CFA = context-insensitive:** one $\hat\rho(x)$ per variable, merged across all call sites →
  cheap but imprecise; **k-CFA** refines this ([17](17-beyond-0cfa-abstract-values-context.md)).

## 5. Peculiarities & connections
- **Two equivalent presentations:** the **Flow Logic** acceptability relation here, and the
  **constraint-based** formulation ([16](16-0cfa-constraint-based-solving.md)) — same solutions,
  different packaging (specification vs solvable constraint system).
- It is an **abstract interpretation**: $\widehat{\mathit{Val}}=\wp(\mathit{Term})$ is the abstract
  domain, `⊧` encodes soundness of the abstract transfer (cf. [08](08-intro-abstract-interpretation.md)).
- Generalises from FUN to concurrency — the **π-calculus** CFA ([18](18-cfa-pi-calculus.md)) reuses
  exactly this "specify acceptable over-approximation" pattern.

## 6. Pros / cons / use cases
- **Pros:** recovers an (approximate) call graph for higher-order code; simple, sound, and the
  basis of all higher-order program analysis; specification is modular (one clause per construct).
- **Cons:** 0-CFA is **context-insensitive** (imprecise for polymorphic/reused functions);
  worst-case cubic to solve; pure CFA ignores data.
- **Use cases:** compiler optimisation (inlining, dead-code, dispatch resolution), type/flow
  analysis for functional and OO languages, security analyses ([19](19-cfa-pi-applications.md)).

---

## 📋 Cheatsheet (complete)

### FUN syntax (labelled)
$$t ::= c \mid x \mid \mathsf{fn}\ x\Rightarrow e_0 \mid \mathsf{fun}\ f\ x\Rightarrow e_0 \mid e_1e_2 \mid \mathsf{if}\ e_0\ e_1\ e_2 \mid \mathsf{let}\ x{=}e_1\ \mathsf{in}\ e_2 \mid e_1\,\mathsf{op}\,e_2,\qquad e::=t^l.$$

### Abstract domains
$$\hat C:\mathit{Lab}\to\widehat{\mathit{Val}}\ (\text{cache}),\quad \hat\rho:\mathit{Var}\to\widehat{\mathit{Val}}\ (\text{env}),\quad \widehat{\mathit{Val}}=\wp(\mathit{Term})\ (\text{sets of }\mathsf{fn}/\mathsf{fun}\text{ terms}).$$

### Acceptability clauses $(\hat C,\hat\rho)\models e$
$$[\textsf{con}]\ \text{true}\qquad [\textsf{var}]\ \hat\rho(x)\subseteq\hat C(l)\qquad [\textsf{fn}/\textsf{fun}]\ \{\mathsf{fn}/\mathsf{fun}\dots\}\subseteq\hat C(l)$$
$$[\textsf{if}]\ \models t_0\wedge\textstyle\bigwedge_{i}(\models t_i\wedge\hat C(l_i)\subseteq\hat C(l))\qquad [\textsf{let}]\ \models t_1\wedge\models t_2\wedge\hat C(l_1)\subseteq\hat\rho(x)\wedge\hat C(l_2)\subseteq\hat C(l)$$
$$[\textsf{app}]\ \models t_1\wedge\models t_2\wedge\!\!\!\bigwedge_{(\mathsf{fn}\,x\Rightarrow t_0^{l_0})\in\hat C(l_1)}\!\!\!\big(\models t_0^{l_0}\wedge\hat C(l_2)\subseteq\hat\rho(x)\wedge\hat C(l_0)\subseteq\hat C(l)\big)$$
$$[\textsf{op}]\ \models t_1\wedge\models t_2\quad(\text{no demand on }\hat C(l):\ \mathsf{op}\text{ returns a base value, like }[\textsf{con}])$$

### Keywords
0-CFA = context-**insensitive**; result over-approximates reachable function flows; acceptable = conservative guess; specification (Flow Logic) not computation; coinductive.
