---
title: Local Completeness Logic (LCL)
abbrev: LCL
lectures: "16 (LCL)"
paper: "R. Bruni, R. Giacobazzi, R. Gori, F. Ranzato — A Logic for Locally Complete Abstract Interpretations, LICS 2021 (distinguished paper) + JACM"
theme: "reconciling correctness (abstract interpretation) and incorrectness (IL) via *local* completeness"
oneliner: "Use an abstract domain to prove a program correct OR produce a genuine (false-alarm-free) bug, whenever the abstraction is complete along the computed states."
render: "Notation is LaTeX math ($…$ / $$…$$). Preview with a KaTeX markdown extension."
---

# Local Completeness Logic (LCL)

**Theme:** the **bridge** between the two halves of the course — the over-approximation
world of [Abstract Interpretation](08-intro-abstract-interpretation.md) and the
under-approximation world of [Incorrectness Logic](02-incorrectness-logic.md). LCL turns an
abstract analysis into a proof system that is **sound for correctness *and* for bug-finding**.

## 1. Purpose & core idea
Abstract interpretation is sound but **incomplete**: an alarm may be a **false alarm**
(§[08](08-intro-abstract-interpretation.md)). LCL's insight: you don't need the abstraction
to be complete *everywhere* — only **locally**, along the states the computation actually
traverses. Under that (much weaker) condition, the analysis becomes **complete enough** to
decide the verification question: it either **proves the program correct** or exhibits a
**true** counterexample — *never* a false alarm. It thus **combines** over-approximation (AI)
with under-approximation ([IL](02-incorrectness-logic.md)).

## 2. Local completeness
Recall the closure $A\triangleq\gamma\circ\alpha$ (an abstract domain seen as a subset of
the concrete, §[09](09-order-theory-galois-connections.md)). **Global** completeness of a
command is $\forall P.\ A([\![  c ]\!] P)=A([\![  c ]\!] A(P))$ — abstracting
inputs first loses nothing. That is rare. **Local completeness** requires it *only at one input*:

> [!important] Local completeness (Def.)
> $c$ is **locally complete** in $A$ for input $P$, written $\mathcal C^A_P(c)$, iff
> $$A([\![  c ]\!] P)\ =\ A([\![  c ]\!] A(P)).$$
> Since always $A([\![  c ]\!] P)\sqsubseteq A([\![  c ]\!] A(P))$, this is
> the reverse inclusion **at $P$ only**. Focus on completeness **along the traversed states**
> (which are collected as an under-approximation). E.g. $b\triangleq(x>0)$ is *globally*
> incomplete in Intervals but *locally* complete for $P=\{-10,0,1,10\}$.

**Why completeness is what matters (for an expressible spec, $A(\mathit{Spec})=\mathit{Spec}$):**
$$[\![  c ]\!] P\subseteq\mathit{Spec}\iff [\![  c ]\!]^\sharp_A A(P)\subseteq\mathit{Spec}\quad(\text{when complete}).$$
So a *complete* abstract analysis decides correctness exactly — no false alarms.
**Sources of incompleteness:** completeness is preserved by $;$, $\cup$, and fixpoints;
**only atomic commands** $e$ introduce it. Assignments are complete in many domains;
**guards are the troublesome case** ($b$ complete $\Rightarrow$ $b,\neg b$ expressible, and the
join of abstract points below them expressible). Incompleteness is **intrinsic to the domain**.

## 3. The LCL triple — combining under + over
> [!important] LCL triple $\vdash_A [P]\,c\,[Q]$ (validity)
> $$A(Q)\ \supseteq\ [\![  c ]\!] P\ \supseteq\ Q.$$
> Two directions at once: **$[\![  c ]\!] P\supseteq Q$** — $Q$ **under-approximates**
> the reachable states (as in [IL](02-incorrectness-logic.md): every state of $Q$ is genuinely
> reachable); **$A(Q)\supseteq[\![  c ]\!] P$** — $A(Q)$ **over-approximates** them,
> and in fact $A(Q)=A([\![  c ]\!] P)$ is a *sound abstract* post. So $Q$ is a
> reachable under-approximation **precise enough that its abstraction is the exact abstract
> semantics**.

## 4. The proof system $\mathrm{LCL}_A$
Every atomic step carries a **local-completeness proof obligation** $\mathcal C^A_P(e)$:

$$\dfrac{\mathcal C^A_P(e)}{\vdash_A [P]\ e\ [[\![  e ]\!] P]}\ [\textsf{transfer}]\qquad \text{(assignment: Floyd's post; test: the IL rule } \vdash_A[P]\,b?\,[P\wedge b]).$$

$$\dfrac{\vdash_A [P]\,c_1\,[R]\quad \vdash_A [R]\,c_2\,[Q]}{\vdash_A [P]\ c_1;c_2\ [Q]}\ [\textsf{seq}]\qquad \dfrac{\vdash_A [P]\,c_1\,[Q_1]\quad \vdash_A [P]\,c_2\,[Q_2]}{\vdash_A [P]\ c_1+c_2\ [Q_1\vee Q_2]}\ [\textsf{join}]$$

$$\dfrac{\vdash_A [P]\,c\,[R]\quad \vdash_A [P\vee R]\,c\,[Q]}{\vdash_A [P]\ c^\star\ [Q]}\ [\textsf{rec}]\qquad \dfrac{\vdash_A [P]\,c\,[Q]\quad Q\Rightarrow A(P)}{\vdash_A [P]\ c^\star\ [P]}\ [\textsf{iterate}]\ (\text{fixpoint acceleration})$$

$$\dfrac{P'\Rightarrow P\Rightarrow A(P')\quad \vdash_A [P']\,c\,[Q']\quad Q\Rightarrow Q'\Rightarrow A(Q)}{\vdash_A [P]\ c\ [Q]}\ [\textsf{relax}]$$

**[relax]** is IL-style (weaken the pre, shrink the post) **but must preserve the abstraction**:
$A(P)=A(P')$ and $A(Q)=A(Q')$ — you may move within an abstract element but not across.
(*Convexity lemma:* if $\mathcal C^A_P(e)$ and $P\Rightarrow R\Rightarrow A(P)$ then $\mathcal C^A_R(e)$.)

## 5. Properties — the verification payoff, soundness, completeness (with *why*)
- **The payoff (why LCL is powerful).** If $\vdash_A [P]\,c\,[Q]$ then for an expressible spec:
  $$[\![  c ]\!] P\subseteq\mathit{Spec}\iff Q\subseteq\mathit{Spec}.$$
  So check the *finite* under-approximation $Q$: if $Q\subseteq\mathit{Spec}$ the program is
  **proved correct**; if $Q\not\subseteq\mathit{Spec}$, any $q\in Q\setminus\mathit{Spec}$ is a
  **true alert** (genuinely reachable) — **no false alarms**. One derivation settles correctness
  *or* yields a real bug.
- **Soundness (logical correctness).** $\vdash_A [P]\,c\,[Q]\Rightarrow A(Q)=A([\![  c ]\!] P)\wedge Q\subseteq[\![  c ]\!] P$. **Why:** each rule maintains the under/over sandwich; local completeness at every atomic step keeps $A(Q)$ equal to the abstract semantics.
- **Logical (in)completeness.** LCL can derive a triple **iff the abstraction is locally
  complete** along the computation. If some traversed atomic command/guard is locally
  *incomplete* in $A$, the $\mathcal C^A_P(e)$ obligation of $[\textsf{transfer}]$ fails and **no
  derivation exists** — *intrinsic logical incompleteness*, a limitation of the **domain**, not
  the logic. Remedy: refine $A$ to a **complete shell** $A_b$ (may blow up; can break other
  operators' completeness).

## 6. Pros / cons / use cases
- **Pros:** unifies correctness and incorrectness in one abstract-interpretation-based logic;
  **repairs AI's false-alarm problem** (alarms are true); needs only *local* completeness
  (far weaker than global); reuses standard abstract domains.
- **Cons:** requires local completeness along the run (guards are often locally incomplete);
  achieving it may force a costly complete-shell refinement; proof obligations must be
  discharged per atomic step.
- **Use cases:** abstract-interpretation-based verification that also **produces genuine
  counterexamples**; the theoretical reconciliation of the two sides of this course
  ([AI/HL](08-intro-abstract-interpretation.md) over-approx vs [IL](02-incorrectness-logic.md) under-approx).

---

## 📋 Cheatsheet (complete)

### Local completeness
$$\mathcal C^A_P(c)\ \overset{\triangle}{\iff}\ A([\![  c ]\!] P)=A([\![  c ]\!] A(P))\quad(\text{always }\sqsubseteq;\ \text{equality required at }P\text{ only}).$$
Preserved by $;,\cup,\mathrm{fix}$; introduced only by **atomic commands**. Guard $b$ complete $\Rightarrow b,\neg b$ expressible $+$ joins below them expressible.

### LCL triple (validity)
$$\vdash_A [P]\,c\,[Q]\ \text{valid}\iff A(Q)\supseteq[\![  c ]\!] P\supseteq Q\quad(\text{under-approx }Q\subseteq[\![  c ]\!] P,\ \text{and }A(Q)=A([\![  c ]\!] P)).$$

### Rules ($\mathrm{LCL}_A$)
$$\dfrac{\mathcal C^A_P(e)}{\vdash_A [P]\,e\,[[\![  e ]\!] P]}\,[\textsf{transfer}]\quad \dfrac{\vdash_A [P]c_1[R]\ \ \vdash_A [R]c_2[Q]}{\vdash_A [P]c_1;c_2[Q]}\,[\textsf{seq}]\quad \dfrac{\vdash_A [P]c_1[Q_1]\ \ \vdash_A [P]c_2[Q_2]}{\vdash_A [P]c_1{+}c_2[Q_1\vee Q_2]}\,[\textsf{join}]$$
$$\dfrac{\vdash_A [P]c[R]\ \ \vdash_A [P\vee R]c[Q]}{\vdash_A [P]c^\star[Q]}\,[\textsf{rec}]\quad \dfrac{\vdash_A [P]c[Q]\ \ Q\Rightarrow A(P)}{\vdash_A [P]c^\star[P]}\,[\textsf{iterate}]\quad \dfrac{P'\Rightarrow P\Rightarrow A(P')\ \ \vdash_A [P']c[Q']\ \ Q\Rightarrow Q'\Rightarrow A(Q)}{\vdash_A [P]c[Q]}\,[\textsf{relax}]$$

### Theorems
- **[Soundness]** $\vdash_A [P]\,c\,[Q]\Rightarrow Q\subseteq[\![  c ]\!] P\ \wedge\ A(Q)=A([\![  c ]\!] P)$.
- **[Verification]** for expressible $\mathit{Spec}$: $\vdash_A [P]c[Q]\Rightarrow([\![  c ]\!] P\subseteq\mathit{Spec}\iff Q\subseteq\mathit{Spec})$. $\;Q\not\subseteq\mathit{Spec}\Rightarrow$ true alert (no false alarm).
- **[Logical completeness]** derivable $\iff$ locally complete along the run; else **intrinsic incompleteness** (domain limitation; use a complete shell $A_b$).

### The reconciliation
$$\underbrace{A(Q)\supseteq[\![  c ]\!] P}_{\text{over-approx (AI / HL)}}\ \wedge\ \underbrace{[\![  c ]\!] P\supseteq Q}_{\text{under-approx (IL)}}\ \Longrightarrow\ \text{prove correct }(Q\subseteq\mathit{Spec})\ \text{or find a true bug }(q\in Q\setminus\mathit{Spec}).$$
