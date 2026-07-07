---
title: CFA for the π-calculus — Applications (Behaviour & Security)
abbrev: CFA (π applications)
lectures: "23 (CFA for π, applications); master deck: CFA-for-Pi"
paper: "Bodei, Degano, Nielson & Nielson — Static analysis for the π-calculus with applications to security, Inform. Comput. 2001"
theme: "using the π-calculus CFA to statically guarantee well-behavedness, well-sortedness, and security (secrecy, non-leaking, taint)"
oneliner: "Extend the analysis with an error component and prove adequacy — statically checkable predicates (empty errors, sort/security constraints on κ̂) that imply the corresponding runtime guarantees."
render: "Notation is LaTeX math ($…$ / $$…$$). Preview with a KaTeX markdown extension."
---

# CFA for the π-calculus — Applications (Behaviour & Security)

**Theme:** the payoff of [18](18-cfa-pi-calculus.md). The communication over-approximation
$(\hat\rho,\hat\kappa)$ is turned into **static guarantees** about a process's behaviour and
**security** — and each is backed by an **adequacy theorem** (static property ⟹ runtime property).
This closes the course: CFA as a practical, sound verification method, and a **flow-based
alternative to type systems**.

## 1. Purpose & core idea
A sound over-approximation of "who communicates what" lets us **rule out bad runtime behaviours
by inspecting the analysis result**. The recurring recipe:
1. define a **dynamic property** on the semantics (what must never happen at runtime),
2. define a **static property** on the analysis $(\hat\rho,\hat\kappa)$ (a checkable condition),
3. prove **adequacy**: *static property ⟹ dynamic property* — so passing the static check
   **guarantees** the runtime property.

To detect mismatches, the analysis is extended with an **error component** $\psi$
(written $(\hat\rho,\hat\kappa)\models_P P:\psi$): $\psi$ collects the channels where a
**communication error** (e.g. arity mismatch) may occur. An **empty $\psi$** means "no error
predicted."

## 2. Behavioural guarantees
- **Well-behavedness** (matching arities). *Dynamic:* every communication that ever fires has
  $|\vec m|=|\vec x|$ (sender/receiver arities agree). *Static:* $\exists(\hat\rho,\hat\kappa).\ (\hat\rho,\hat\kappa)\models_P P^\ast:\varnothing$
  (a valid analysis with **empty error component**). **Adequacy:** statically well-behaved ⟹
  dynamically well-behaved — *no runtime arity/communication mismatch can occur*.
- **Well-sortedness** (channels carry values of a fixed shape). A **sorting** $\Sigma:\mathit{Sort}\to\mathit{Sort}^\ast$
  assigns each channel the arity **and** sorts of what it may carry. *Static:* $\models_P P^\ast:\varnothing$
  **and** for every constant $n$, $\ \sigma(\hat\kappa(n))\subseteq\{\Sigma(\sigma(n))\}$ — everything
  CFA predicts on channel $n$ has the prescribed shape. **Adequacy:** static ⟹ dynamic
  well-sortedness (no arity/sort mismatch).

## 3. Security guarantees
The same pattern enforces **confidentiality** by classifying names and constraining $\hat\kappa$:
- **Secrecy-preserving** (2-level). A mapping $\Sigma:\mathit{Const}\to\{\mathsf{secret},\mathsf{public}\}$.
  *Property:* a secret name is **never sent on a public channel**. *Static:* a valid analysis whose
  $\hat\kappa$ satisfies $\ \Sigma(n)=\mathsf{public}\Rightarrow\forall \vec m\in\hat\kappa(n):\Sigma(\vec m)=\mathsf{public}$.
  **Adequacy:** static ⟹ *no secret information flows through public channels* ("no write-down").
- **Non-leaking** (a **security lattice**). Levels with $\mathsf{low}\sqsubseteq\mathsf{high}$ via
  $\Lambda:\mathit{Const}\to\mathit{Levels}$; *property:* the level of a message never exceeds the
  level of its channel (only low info on low channels). Static condition on $\hat\kappa$ + adequacy —
  a multi-level confidentiality guarantee.
- **Taint analysis** (the dual). Classify names **tainted/untainted**; **taint-safety** = untainted
  (trusted) channels never carry tainted (untrusted) data. Static predicate on $\hat\kappa$ + adequacy
  ⟹ taint-safe process. (Integrity mirror of secrecy.)

## 4. CFA vs type systems (the connecting insight)
Each application is a **flow-logic analogue of a type system**: the static property plays the role
of *typing*, and **adequacy is the analogue of type soundness** (well-typed/analysed ⟹ good
behaviour). CFA is more *flexible* (flow-based, no explicit annotations, uniform recipe across
properties) while giving the same kind of guarantee — the course's final message that **static
analysis and type systems are two faces of the same "predicate preserved by execution" idea**
(cf. the subject-reduction proofs of [14](14-0cfa-semantic-correctness.md), [18](18-cfa-pi-calculus.md)).

## 5. Properties
- **Soundness throughout:** every guarantee rests on an **adequacy theorem** proved from the CFA's
  subject-reduction correctness — static success is never a false assurance (no false negatives).
- **Incompleteness (false alarms):** being over-approximate, the static check may **reject a safe
  process** (predict an error/leak that cannot happen) — the usual over-approximation trade-off.
- **Uniformity:** one analysis $(\hat\rho,\hat\kappa,\psi)$, many properties — each is just a
  different *reading/constraint* on the same result.

## 6. Pros / cons / use cases
- **Pros:** turns one CFA into **many sound verifications**; automatic; a principled,
  type-system-strength method for concurrent/mobile systems; classic security policies (secrecy,
  integrity/taint) fall out.
- **Cons:** over-approximation ⇒ false alarms; models are idealised (π-calculus); precision limited
  by 0-CFA.
- **Use cases:** static verification of security protocols and concurrent systems — information-flow
  confidentiality (no-read-up/no-write-down), integrity/taint tracking, arity/sort safety.

---

## 📋 Cheatsheet (complete)

### Method (every application)
$$\text{dynamic property (semantics)}\ \xLeftarrow{\ \textbf{adequacy}\ }\ \text{static property on }(\hat\rho,\hat\kappa[,\psi]).\qquad \text{static} \Rightarrow \text{dynamic (sound; may over-reject).}$$
Error component: $(\hat\rho,\hat\kappa)\models_P P:\psi$, $\psi$ = predicted error channels; empty $\psi$ = no error.

### Behaviour
$$\textbf{well-behaved: }\ \models_P P^\ast:\varnothing\ \Rightarrow\ \text{arities always match.}$$
$$\textbf{well-sorted: }\ \models_P P^\ast:\varnothing\ \wedge\ \forall n.\ \sigma(\hat\kappa(n))\subseteq\{\Sigma(\sigma(n))\}\ \Rightarrow\ \text{sorts always match},\quad \Sigma:\mathit{Sort}\to\mathit{Sort}^\ast.$$

### Security
$$\textbf{secrecy: }\ \Sigma(n){=}\mathsf{public}\Rightarrow\forall\vec m\in\hat\kappa(n):\Sigma(\vec m){=}\mathsf{public}\ \Rightarrow\ \text{no secret on public channel (no write-down)}.$$
$$\textbf{non-leaking: }\ \text{security lattice }\Lambda,\ \mathsf{low}\sqsubseteq\mathsf{high};\ \text{msg level}\le\text{channel level}.\qquad \textbf{taint: }\ \text{untainted channels carry no tainted data (dual)}.$$

### Connection
Static property ≈ typing; **adequacy ≈ type soundness**; CFA = flexible, flow-based alternative to type systems.
