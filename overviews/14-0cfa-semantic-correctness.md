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
$\rho\vdash ie\to ie'$ (one step of computing $ie$ under concrete environment $\rho$). Two
deliberate design choices make the semantics **match the CFA abstraction**:
- **Explicit environments, not substitution.** A configuration carries a concrete environment
  $\rho$; we *bind* variables rather than substitute. (Substitution would copy/rename function
  terms and **lose the identity of functions** — but abstract values *are* sets of function
  terms, so their identity must be preserved.)
- **Closures.** A function evaluates to a **closure** $t^\rho$ = the function term $t$ together
  with the environment $\rho$ capturing its free variables (static/lexical binding).

$$v ::= c \mid t^\rho\ (\text{closure})\qquad \rho ::= [\,] \mid \rho[x\mapsto v]\qquad ie ::= it^l\ (\text{intermediate expressions/terms, incl. } \rho{:}ie\ \text{frames and closures}).$$

## 3. The agreement relation between concrete and abstract environments
Correctness needs the concrete environment $\rho$ and the abstract one $\hat\rho$ to **agree** —
every concrete binding is reflected abstractly. Define $\rho\,\mathcal R\,\hat\rho$:

$$\rho\,\mathcal R\,\hat\rho \iff \mathrm{dom}(\rho)\subseteq\mathrm{dom}(\hat\rho)\ \wedge\ \forall x\in\mathrm{dom}(\rho):\ \rho(x)=t_x^{\rho_x}\ \Rightarrow\ \big(t_x\in\hat\rho(x)\ \wedge\ \rho_x\,\mathcal R\,\hat\rho\big).$$

In this context $\text{dom}$ is the function that records each variable which possesses an association in the domain $\rho$ or $\hat{\rho}$

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

### Agreement (concrete $\rho$ vs abstract $\hat\rho$)
$$\rho\,\mathcal R\,\hat\rho \iff \mathrm{dom}(\rho)\subseteq\mathrm{dom}(\hat\rho)\ \wedge\ \forall x:\ \rho(x)=t_x^{\rho_x}\Rightarrow t_x\in\hat\rho(x)\wedge\rho_x\,\mathcal R\,\hat\rho.$$

### Theorem
$$\textbf{[Subject reduction]}\quad \rho\,\mathcal R\,\hat\rho\ \wedge\ (\hat C,\hat\rho)\models ie\ \wedge\ \rho\vdash ie\to ie'\ \Longrightarrow\ (\hat C,\hat\rho)\models ie'.$$
$$\textbf{[Soundness corollary]}\quad \text{every acceptable }(\hat C,\hat\rho)\text{ over-approximates all reachable function flows.}$$

### Keywords
subject reduction = preservation of acceptability; explicit environments + closures (not substitution) to keep function identity; correctness of *any* acceptable guess.
