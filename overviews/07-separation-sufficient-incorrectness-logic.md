---
title: Separation Sufficient Incorrectness Logic (SepSIL)
abbrev: SepSIL
lectures: "10 (Incorrectness Separation Logic / Separation SIL)"
paper: "F. Ascari, R. Bruni, R. Gori, F. Logozzo — Revealing Sources of (Memory) Errors via Backward Analysis, OOPSLA 2025"
quadrant: "backward · under-approximation · heap/local"
oneliner: "SIL + SL: local backward reasoning that reveals the SOURCE states leading to memory errors."
render: "Notation is LaTeX math ($…$ / $$…$$). Preview with a KaTeX markdown extension."
---

# Separation Sufficient Incorrectness Logic (SepSIL)

**Quadrant:** backward · under-approximation, over the **heap** with **local reasoning**.
$$\textbf{SepSIL} = \textbf{SIL} + \textbf{SL}.$$

## 1. Purpose & core idea
SepSIL is the **heap-aware, backward** memory-bug logic: it combines
[SIL](04-sufficient-incorrectness-logic.md)'s ability to reveal the **source** of an error
with [SL](05-separation-logic.md)'s **local reasoning**. Where
[ISL](06-incorrectness-separation-logic.md) (forward) proves *that* a memory error is
reachable, SepSIL (backward) characterises the **initial states that lead to it** — and,
per the paper, yields **more succinct postconditions** and **stronger guarantees** than ISL.

## 2. Basic definition
A SepSIL triple is a SIL triple over heap-states, closed under the separating frame:

$$\langle P\rangle\,c\,\langle Q\rangle\ \text{ valid}\iff P\subseteq[\![  c ]\!]^{op}Q,\qquad \dfrac{\langle P\rangle\,c\,\langle Q\rangle}{\langle P\ast R\rangle\,c\,\langle Q\ast R\rangle}\ [\textsf{frame}].$$

Reading: **every** heap-state in $P$ has **at least one** execution reaching the memory
error $Q$ — so $P$ characterises **sufficient sources** of the error. It reuses ISL's
deallocated-cell predicate $x\not\mapsto$ in its assertion language.

## 3. Over/under-approximation & information propagation
**Backward, under-approximation, local.** You start from the error postcondition and pull
back — via **weakest-precondition-style local axioms** and the frame rule — a subset of
genuinely-responsible source states. The result is a **stronger, more succinct** statement
than ISL's forward post: *any state in the precondition can lead to the error.*

## 4. Peculiarities & differences vs siblings
- **Backward Hoare/weakest-pre local axioms.** Because SepSIL is backward, its atomic
  axioms are weakest-precondition shaped and apply to any post (e.g. write
  $\langle x\mapsto\_\rangle\,[x]{:=}y\,\langle x\mapsto y\rangle$), dispose
  $\langle x\mapsto\_\rangle\,\mathsf{free}(x)\,\langle x\not\mapsto\rangle$.
- **vs ISL (the headline comparison).** On the same use-after-free, ISL gives a forward
  $er$ result; SepSIL gives $\langle v\mapsto a\ast a\mapsto\_\ast\text{true}\rangle\,c\,\langle x\not\mapsto\_\ast\text{true}\rangle$
  — a **more succinct** post and the **stronger** reading "*any* state in the pre can lead
  to the error."
- **Same consequence direction as SIL/HL:** strengthen the pre, weaken the post.
- Reuses SL's $\ast$/frame and ISL's $\not\mapsto$ (deallocated cells).

## 5. Properties: soundness & completeness (with *why*)
- **Sound** (induction on the derivation): $\vdash\langle P\rangle\,c\,\langle Q\rangle\Rightarrow P\subseteq[\![  c ]\!]^{op}Q$.
- **(Relatively) complete.** Any valid SepSIL triple is derivable. **Why it is delicate:**
  completeness "relies on a careful crafting of **both the assertion language** (notably
  $\not\mapsto$, to keep the heap monotonic) **and the rules for atomic commands**" — the
  same monotonic-heap idea that saved ISL, now in the backward direction.

## 6. Pros / cons / use cases
- **Pros:** **backward**, local, no-false-positive **source** analysis for memory errors;
  more succinct posts + stronger guarantees than ISL; sound and (relatively) complete.
- **Cons:** the newest and most technical of the family; needs the carefully-crafted
  assertion language.
- **Use cases:** automated **backward** reasoning about pointer / dynamic-memory programs to
  locate the **origin** of memory errors.

---

## 📋 Cheatsheet (complete)

### Validity + frame
$$\langle P\rangle\,c\,\langle Q\rangle\ \text{valid}\iff P\subseteq[\![  c ]\!]^{op}Q,\qquad \dfrac{\langle P\rangle\,c\,\langle Q\rangle}{\langle P\ast R\rangle\,c\,\langle Q\ast R\rangle}\ [\textsf{frame}]\ (\mathrm{FV}(R)\cap\mathrm{Mod}(c)=\varnothing).$$
Assertions include SL's $\mathsf{emp},\ \mapsto,\ \ast$ plus ISL's $x\not\mapsto$ (deallocated cell).

### Local axioms (backward / weakest-precondition style)
$$\dfrac{}{\langle x\mapsto\_\rangle\ [x]:=y\ \langle x\mapsto y\rangle}\ [\textsf{write}] \qquad \dfrac{}{\langle y\mapsto v\wedge v{=}x'\rangle\ x:=[y]\ \langle y\mapsto v\wedge x{=}x'\rangle}\ [\textsf{read}]$$
$$\dfrac{}{\langle\mathsf{emp}\rangle\ x:=\mathsf{alloc}()\ \langle x\mapsto\_\rangle}\ [\textsf{alloc}] \qquad \dfrac{}{\langle x\mapsto\_\rangle\ \mathsf{free}(x)\ \langle x\not\mapsto\rangle}\ [\textsf{free}]$$
$$\dfrac{}{\langle\Phi[a/x]\rangle\ x:=a\ \langle\Phi\rangle}\ [\textsf{assign}] \qquad \dfrac{}{\langle\Phi\wedge b\rangle\ b?\ \langle\Phi\rangle}\ [\textsf{assume}]$$

### Structural rules
$$\dfrac{\langle P'\rangle\,c\,\langle Q'\rangle\ \text{with}\ P'\Leftarrow P,\ Q\Leftarrow Q'}{\langle P\rangle\,c\,\langle Q\rangle}\ [\textsf{cons}] \qquad \dfrac{\langle P\rangle\,c\,\langle Q\rangle\ \ G\notin\mathrm{FV}(r)}{\langle\exists G.\,P\rangle\,c\,\langle\exists G.\,Q\rangle}\ [\textsf{exists}]$$

### vs ISL — same bug, two readings
$$\text{ISL (fwd): }\ [v\mapsto a\ast a\mapsto\_]\,c\,[er:\exists a'.\ v\mapsto a'\ast a'\mapsto\_\ast a\not\mapsto]$$
$$\text{SepSIL (bwd): }\ \langle v\mapsto a\ast a\mapsto\_\ast\text{true}\rangle\,c\,\langle x\not\mapsto\_\ast\text{true}\rangle\quad(\text{more succinct; any pre-state leads to the error})$$

### Theorems
- **[Soundness]** $\vdash\langle P\rangle\,c\,\langle Q\rangle\Rightarrow P\subseteq[\![  c ]\!]^{op}Q$.
- **[(Relative) completeness]** every valid SepSIL triple is derivable — relies on the crafted assertion language ($\not\mapsto$, monotonic heap) and atomic rules.

### Consequence direction
Strengthen the pre, weaken the post (as in SIL / HL).
