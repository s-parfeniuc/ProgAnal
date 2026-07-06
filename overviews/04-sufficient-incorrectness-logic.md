---
title: Sufficient Incorrectness Logic (SIL)
abbrev: SIL
lectures: "08 (Sufficient Incorrectness Logic)"
paper: "F. Ascari, R. Bruni, R. Gori, F. Logozzo, Revealing Sources of (Memory) Errors via Backward Analysis, OOPSLA 2025"
quadrant: "backward · under-approximation"
oneliner: "Reveal the SOURCE of a bug — initial states each of which is sufficient to trigger the error."
render: "Notation is LaTeX math ($…$ / $$…$$). Preview with a KaTeX markdown extension."
---

# Sufficient Incorrectness Logic (SIL)

**Quadrant:** backward · under-approximation ⟶ reveals the **source** of bugs.
*Note: SIL is **not** a separation logic; the heap version is [SepSIL](07-separation-sufficient-incorrectness-logic.md).*

## 1. Purpose & core idea
SIL fills the **fourth quadrant** (backward + under) left open by HL/IL/NC. Where
[IL](02-incorrectness-logic.md) proves *that* an error is reachable, SIL identifies the
**initial states responsible** for it — the *source*. This matters because IL, being
forward, records path/error conditions in the *result* and cannot precisely characterise
which inputs cause the bug. SIL reasons **backward from the error**, so its precondition
*is* the characterisation of the responsible inputs.

## 2. Basic definition
Taking $Q$ = the set of **error** states:

$$\langle P\rangle\,c\,\langle Q\rangle\ \text{ valid}\quad\overset{\triangle}{\iff}\quad P\subseteq\llbracket c\rrbracket^{op}Q \quad\iff\quad \forall\sigma\in P.\ \exists\delta\in Q.\ \delta\in\llbracket c\rrbracket\sigma.$$

Reading: **every** state in $P$ has **at least one** execution reaching an error in $Q$.
So each state of $P$ is a **sufficient condition for incorrectness** — a genuine trigger.
(These are also known as *Lisbon triples* in the outcome-logic literature.)

## 3. Over/under-approximation & information propagation
**Backward, under-approximation.** You start from the error postcondition and pull back a
**subset** of the pre-image — states each of which *can* cause the error. Because it
under-approximates, the reported sources are **genuine** (no false positives): every
$\sigma\in P$ really can crash.

## 4. Peculiarities & differences vs siblings
- **Manifest errors.** An error that occurs *regardless of context* cannot be
  characterised by IL, but SIL captures it cleanly: $Q$ is a **manifest error** $\iff
  \langle\text{true}\rangle\,c\,\langle Q\rangle$ is valid (every initial state reaches it).
- **IL post $\leftrightarrow$ SIL pre.** For a bug requiring $even(x)\wedge odd(y)$: IL
  derives $[z{=}11]\,c\,[er:\,z{=}42\wedge odd(y)\wedge even(x)]$ (conditions in the *post*);
  SIL derives $\langle z{=}11\wedge odd(y)\wedge even(x)\rangle\,c\,\langle z{=}42\rangle$
  (the *responsible inputs* in the *pre*).
- **HL/SIL coincide for deterministic, terminating $c$:** $\langle P\rangle\,c\,\langle Q\rangle\iff\{P\}\,c\,\{Q\}$.
- **Hoare's backward assignment axiom is sound here** (it was *unsound* for IL) — SIL is a
  backward logic, so backward substitution is its natural axiom.
- **Same consequence direction as HL:** strengthen the pre (drop error-source disjuncts),
  weaken the post.

## 5. Properties: soundness & completeness (with *why*)
- **Sound and complete.** SIL is a **minimal, sound, and complete** proof system for
  Lisbon triples. **Why completeness is clean (like IL):** assertions are sets of states
  and implication is inclusion; the backward under-approximate reading composes without the
  finiteness obstruction.
- **$\langle\textsf{conj}\rangle$ is unsound** (as in IL): from $\langle x{=}0\rangle\,x{:=}?\,\langle x{=}0\rangle$
  and $\langle x{=}0\rangle\,x{:=}?\,\langle x{=}1\rangle$ one would derive
  $\langle x{=}0\rangle\,x{:=}1\,\langle\text{false}\rangle$, which is invalid.
- **The forward assume axiom is *invalid*:** $\langle P\rangle\,b?\,\langle P\wedge b\rangle$
  fails (e.g. $\langle x\ge 0\rangle\,(x{>}1)?\,\langle x\ge 2\rangle$ is false — from $x{=}0$
  you cannot reach $x\ge 2$). The correct rule is **backward**: $\langle Q\wedge b\rangle\,b?\,\langle Q\rangle$.

## 6. Pros / cons / use cases
- **Pros:** points at the **root cause** (responsible inputs); characterises **manifest
  errors**; sound **and** complete; foundation for [SepSIL](07-separation-sufficient-incorrectness-logic.md).
- **Cons:** $\langle\textsf{conj}\rangle$ unsound; newer/less tooling than IL.
- **Use cases:** backward bug-source analysis; explaining *why* / *from where* a bug happens.

---

## 📋 Cheatsheet (complete)

### Validity
$$\langle P\rangle\,c\,\langle Q\rangle\ \text{valid}\iff P\subseteq\llbracket c\rrbracket^{op}Q\iff\forall\sigma\in P.\ \exists\delta\in Q.\ \delta\in\llbracket c\rrbracket\sigma.$$
where $\llbracket c\rrbracket^{op}Q=\{\sigma\mid\llbracket c\rrbracket\sigma\cap Q\neq\varnothing\}=wpp(c,Q)$ (backward / weakest possible precondition).

### Axioms & inference rules (backward-oriented, from the error post)

$$\dfrac{}{\langle Q[a/x]\rangle\ x:=a\ \langle Q\rangle}\ [\textsf{Hoare-assign}] \qquad \dfrac{}{\langle Q\wedge b\rangle\ b?\ \langle Q\rangle}\ [\textsf{assume}]$$

$$\dfrac{\langle P_1\rangle\,c_1\,\langle Q\rangle\quad \langle P_2\rangle\,c_2\,\langle Q\rangle}{\langle P_1\vee P_2\rangle\ c_1+c_2\ \langle Q\rangle}\ [\textsf{choice}] \qquad \dfrac{\forall n\ge 0.\ \langle Q_{n+1}\rangle\,c\,\langle Q_n\rangle}{\langle\exists k.\,Q_k\rangle\ c^\star\ \langle Q_0\rangle}\ [\textsf{iter, backward}]$$

$$\dfrac{\langle P\rangle\,c\,\langle Q\rangle}{\langle P\vee R\rangle\,c\,\langle Q\rangle}\ [\textsf{drop-disjunct (pre)}] \qquad \dfrac{P'\Rightarrow P\quad \langle P'\rangle\,c\,\langle Q'\rangle\quad Q\Rightarrow Q'}{\langle P\rangle\,c\,\langle Q\rangle}\ [\textsf{cons}]$$

(Note: $[\textsf{drop-disjunct}]$ read bottom-up *shrinks* the pre — the SIL analog of focusing on fewer error sources.)

### Manifest errors
$$Q\ \text{is a manifest error}\quad\iff\quad \langle\text{true}\rangle\,c\,\langle Q\rangle\ \text{is valid}.$$

### Theorems / key facts
- **[Soundness]** $\vdash\langle P\rangle\,c\,\langle Q\rangle\Rightarrow P\subseteq\llbracket c\rrbracket^{op}Q$.
- **[Completeness]** every valid Lisbon triple is derivable (minimal core rules).
- **[HL equivalence]** if $c$ deterministic and terminating: $\langle P\rangle\,c\,\langle Q\rangle\iff\{P\}\,c\,\{Q\}$.
- **[$\langle\textsf{conj}\rangle$ unsound]**; **[forward assume $\langle P\rangle b?\langle P\wedge b\rangle$ invalid]**.

### Consequence direction
Strengthen the pre (drop error-source disjuncts), weaken the post (same as HL).
