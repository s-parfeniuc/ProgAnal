---
title: 0-CFA — Semantic Correctness (SOS & Subject Reduction)
abbrev: CFA (correctness)
lectures: "18 (CFA — theoretical properties)"
paper: "Nielson, Nielson & Hankin, Principles of Program Analysis, Ch. 3"
theme: "proving that an acceptable CFA guess is a sound description of every execution"
oneliner: "Correctness = subject reduction: acceptability (Ĉ,ρ̂) ⊧ ie is preserved by every evaluation step, so the analysis stays sound as the program runs."
render: "Notation is LaTeX math ($…$ / $$…$$). Preview with a KaTeX markdown extension."
---

# 0-CFA — Semantic Correctness (SOS & Subject Reduction)

**Theme:** why an **acceptable** guess (from [13](13-cfa-motivation-0cfa-specification.md)) is
actually **correct** — a sound over-approximation of the real runtime behaviour. The proof is a
**subject-reduction** argument against a small-step semantics of FUN.

## 1. Purpose & core idea
The acceptability relation only *declares* what a safe guess is. Correctness must **connect it to
execution**: if $(\hat C,\hat\rho)\models e$, then whenever the program runs, the functions it
actually produces at each point are among those the analysis recorded. The technique is
**subject reduction**: show acceptability is **invariant under evaluation** — each computation
step maps an acceptable configuration to an acceptable one. Then, by induction over a whole run,
the initial guess describes every reachable state.

## 2. Setup — a small-step semantics with explicit environments & closures
To reason about correctness we give FUN a **small-step Structural Operational Semantics**
$\rho\vdash ie\to ie'$: *"under concrete environment $\rho$, expression $ie$ does one step of
computation, becoming $ie'$."* Iterating this ($\to^\ast$) runs the program. Two deliberate
design choices make the semantics **match the CFA abstraction**:
- **Explicit environments, not substitution.** A configuration carries a concrete environment
  $\rho$ (a list of variable→value bindings); we *bind* variables rather than substitute. (The
  usual textbook semantics would substitute the argument into the body. But substitution would
  **copy and rename function terms**, destroying the **identity of functions** — and abstract
  values *are* sets of function terms $\wp(\mathit{Term})$, so that identity is exactly what the
  analysis tracks and must be preserved.)
- **Closures.** A function definition evaluates to a **closure** $t^\rho$ = the function term
  $t$ paired with the environment $\rho$ that captures the values of its **free variables** at
  definition time (static/lexical scoping). A closure is a *value*, not something to reduce
  further.

**Values and environments.** A value is either a constant or a closure; an environment is a
finite list of bindings, and $\operatorname{dom}(\rho)$ is the set of variables it binds:
$$v ::= c \mid t^\rho\ (\text{closure})\qquad \rho ::= [\,] \mid \rho[x\mapsto v]$$
$$\operatorname{dom}([\,]) = \emptyset\qquad \operatorname{dom}(\rho[x\mapsto v]) = \operatorname{dom}(\rho)\cup\{x\}.$$
So $\operatorname{dom}(\rho)$ = the variables currently in scope. (It is used in the agreement
relation §3, where we require $\operatorname{dom}(\rho)\subseteq\operatorname{dom}(\hat\rho)$:
every concretely-bound variable is also described abstractly. $\hat\rho$ is a *total* abstract
environment, so this is really "every in-scope variable has an abstract entry.")

**What the intermediate expressions $ie$ represent.** Source expressions alone cannot describe a
program *mid-execution*: once we start evaluating a function body we need to remember *which
environment* it runs in, and a partly-evaluated function has become a closure. So we enlarge the
syntax of source terms into **intermediate expressions** $ie = it^l$ (a labelled intermediate
term) — the **runtime configurations** the small-step relation walks through. Beyond ordinary
source constructs, $it$ adds two things:
- **Closures $t^\rho$** — the *result* of evaluating a function definition (see above).
- **Environment-binding frames $\rho{:}ie$** — read *"evaluate $ie$ under environment $\rho$."*
  These appear when we enter a new scope without substituting: applying a closure
  $(\lambda x. e_1)^{\rho_1}$ to a value $v_2$ steps to the frame $\big(\rho_1[x\mapsto v_2]\big){:}e_1$,
  i.e. "run the body $e_1$ in the captured environment extended with $x\mapsto v_2$" (and a `let`
  behaves the same way). The frame is exactly how explicit-environment semantics records a
  binding that substitution would have performed by copying.

So an $ie$ is a snapshot of the machine: a mix of not-yet-evaluated source subterms, already-computed
closures/constants, and $\rho{:}ie$ frames marking which scope each subterm lives in. Correctness
(§4) is the statement that an acceptable guess stays acceptable for *every* such snapshot.

## 3. The agreement relation between concrete and abstract environments
Correctness needs the concrete environment $\rho$ and the abstract one $\hat\rho$ to **agree** —
every concrete binding is reflected abstractly. Define $\rho\,\mathcal R\,\hat\rho$:

$$\rho\,\mathcal R\,\hat\rho \iff \mathrm{dom}(\rho)\subseteq\mathrm{dom}(\hat\rho)\ \wedge\ \forall x\in\mathrm{dom}(\rho):\ \rho(x)=t_x^{\rho_x}\ \Rightarrow\ \big(t_x\in\hat\rho(x)\ \wedge\ \rho_x\,\mathcal R\,\hat\rho\big).$$

I.e. if $x$ is concretely bound to a closure over term $t_x$, then $t_x$ is in $\hat\rho(x)$ and
the captured environment also agrees (a coinductive/recursive condition on closures).

## 4. Subject reduction — the correctness theorem (with *why*)
> [!important] Subject reduction (semantic correctness)
> If $\ \rho\,\mathcal R\,\hat\rho\ $ and $\ (\hat C,\hat\rho)\models ie\ $ and $\ \rho\vdash ie\to ie'\ $, then $\ (\hat C,\hat\rho)\models ie'.$
>
> **Acceptability is preserved by every evaluation step.** By induction on a full derivation
> $ie\to^\ast ie'$, an acceptable guess for the initial expression stays acceptable for every
> intermediate configuration — so $\hat C$/$\hat\rho$ **soundly over-approximate the reachable
> functions at every program point throughout the run.** *Why it holds:* the delicate step is
> application — but $[\textsf{app}]$ was designed precisely so that when the callee's body starts
> executing, the argument is already in $\hat\rho(x)$ and the body's result flows to the call
> site; the explicit-environment semantics keeps function identities intact so the abstract sets
> remain valid.

**Corollary (soundness).** Any acceptable $(\hat C,\hat\rho)$ is a correct 0-CFA: no runtime
function flow is ever missed. This justifies using *any* acceptable guess — and motivates
computing the **least** one ([15](15-0cfa-existence-least-solutions.md)).

## 5. Peculiarities & connections
- **Why explicit environments matter:** they are the concrete counterpart of $\hat\rho$ and keep
  **function identity** stable, which is exactly what abstract values ($\wp(\mathit{Term})$) track.
- Subject reduction is the same "preservation" pattern used for **type soundness** — CFA
  acceptability plays the role of a typing judgement that is preserved by reduction.
- The analogous correctness result for the concurrent case is in [18](18-cfa-pi-calculus.md).

## 6. Pros / cons / use cases
- **Pros:** a clean, once-and-for-all soundness guarantee for the whole family of acceptable
  solutions; modular (one preservation case per SOS rule).
- **Cons:** requires an explicit-environment/closure semantics tailored to the abstraction; the
  agreement relation on closures is subtle (coinductive).
- **Use cases:** the theoretical warrant that CFA-based optimisations/analyses are safe.

---

## 📋 Cheatsheet (complete)

### Semantic objects
$$v ::= c \mid t^\rho\ (\text{closure});\qquad \rho ::= [\,]\mid\rho[x\mapsto v];\qquad \rho\vdash ie\to ie'\ (\text{small-step, explicit environments}).$$
$$ie ::= it^l\ \text{— runtime configs, adding closures } t^\rho \text{ and env-frames } \rho{:}ie\ (\text{"run } ie \text{ under } \rho\text{")}.$$
$$\operatorname{dom}([\,]) = \emptyset;\qquad \operatorname{dom}(\rho[x\mapsto v]) = \operatorname{dom}(\rho)\cup\{x\}\quad(\text{variables in scope}).$$

### Agreement (concrete $\rho$ vs abstract $\hat\rho$)
$$\rho\,\mathcal R\,\hat\rho \iff \mathrm{dom}(\rho)\subseteq\mathrm{dom}(\hat\rho)\ \wedge\ \forall x:\ \rho(x)=t_x^{\rho_x}\Rightarrow t_x\in\hat\rho(x)\wedge\rho_x\,\mathcal R\,\hat\rho.$$

### Theorem
$$\textbf{[Subject reduction]}\quad \rho\,\mathcal R\,\hat\rho\ \wedge\ (\hat C,\hat\rho)\models ie\ \wedge\ \rho\vdash ie\to ie'\ \Longrightarrow\ (\hat C,\hat\rho)\models ie'.$$
$$\textbf{[Soundness corollary]}\quad \text{every acceptable }(\hat C,\hat\rho)\text{ over-approximates all reachable function flows.}$$

### Keywords
subject reduction = preservation of acceptability; explicit environments + closures (not substitution) to keep function identity; correctness of *any* acceptable guess.
