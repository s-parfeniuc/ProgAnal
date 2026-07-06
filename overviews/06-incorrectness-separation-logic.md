---
title: Incorrectness Separation Logic (ISL)
abbrev: ISL
lectures: "10 (Incorrectness Separation Logic)"
paper: "A. Raad, J. Berdine, H.-H. Dang, D. Dreyer, P. O'Hearn, J. Villard — Local Reasoning About the Presence of Bugs, CAV 2020"
quadrant: "forward · under-approximation · heap/local"
oneliner: "IL + SL: local, compositional bug-catching for memory-safety errors, with no false positives."
render: "Notation is LaTeX math ($…$ / $$…$$). Preview with a KaTeX markdown extension."
---

# Incorrectness Separation Logic (ISL)

**Quadrant:** forward · under-approximation, over the **heap** with **local reasoning**.
$$\textbf{ISL} = \textbf{IL} + \textbf{SL}.$$

## 1. Purpose & core idea
ISL transfers **local, compositional reasoning** (from [SL](05-separation-logic.md)) to
**bug-catching** (from [IL](02-incorrectness-logic.md)): *"local reasoning about the
presence of bugs."* It targets **memory-safety** errors — null-dereference,
**use-after-free**, double-free — and inherits IL's **no-false-positives** guarantee:
every reported bug is real. It is the theory behind Meta's Pulse.

## 2. Basic definition
An ISL triple is an IL triple over heap-states, closed under the separating frame:

$$[P]\,c\,[\varepsilon:Q]\ \text{ valid}\iff Q\subseteq\llbracket c\rrbracket_\varepsilon P,\qquad \dfrac{[P]\,c\,[\varepsilon:Q]}{[P\ast R]\,c\,[\varepsilon:Q\ast R]}\ [\textsf{frame}].$$

$\varepsilon\in\{ok,er\}$ as in IL. The key new **assertion is $x\not\mapsto$**: "$x$ points
to a **deallocated** cell" ($\mathrm{dom}(h)=\{s(x)\}$, $h(s(x))=\bot$). Tracking
deallocated cells (rather than dropping them) is what makes ISL work.

## 3. Over/under-approximation & information propagation
**Forward, under-approximation, local.** Reason on the small footprint; $ok$ carries the
good prefix forward, $er$ collects the reachable **memory-error** states; frame the
untouched heap. A non-$\text{false}$ $er$ result proves a **real, reachable** memory bug.

## 4. Peculiarities & differences vs siblings — the $x\not\mapsto$ fix
- **The naive frame rule is *unsound* in an under-approx heap setting.** From
  $[x\mapsto v]\,\mathsf{free}(x)\,[ok:\mathsf{emp}]$, framing $x\mapsto v$ and applying
  $[\textsf{cons}]$ "derives" $[\text{false}]\,\mathsf{free}(x)\,[ok:x\mapsto v]$ — invalid.
  **Cause:** SL's $\mathsf{free}$ **shrinks** resources (loses the cell).
- **The fix — a monotonic heap.** ISL makes $\mathsf{free}(x)$ yield $[ok:x\not\mapsto]$
  (the cell is **tracked as deallocated**), so **resources never shrink**. This makes the
  frame rule sound *and* **recovers completeness** (the footprint theorem holds). It also
  lets ISL express the very bugs it targets: **use-after-free** $[x\not\mapsto]\,[x]{:=}y\,[er:x\not\mapsto]$,
  **double-free** $[x\not\mapsto]\,\mathsf{free}(x)\,[er:x\not\mapsto]$, and reuse of freed
  addresses $[y\not\mapsto]\,x{:=}\mathsf{alloc}()\,[ok:x\mapsto v\wedge x{=}y]$.
- **Reversed consequence (from IL):** weaken pre, strengthen post — so **local axioms must
  speak *precisely*** (a minimal, exact footprint), unlike SL's axioms which "can speak broadly."

## 5. Properties: soundness & completeness (with *why*)
- **Sound** (induction on the derivation): $\vdash[P]\,c\,[\varepsilon:Q]\Rightarrow Q\subseteq\llbracket c\rrbracket_\varepsilon P$.
- **Complete (footprint theorem).** Any valid ISL triple $[\sigma_P]\,c\,[\varepsilon:\sigma_Q]$
  is derivable. **Why it holds here but *fails* in plain SL:** the $x\not\mapsto$ predicate
  keeps the heap **monotonic** (no information lost at $\mathsf{free}$), which is exactly the
  ingredient SL lacked. So the same idea fixes soundness of frame *and* completeness.
- **$[\ast\textsf{conj}]$ is unsound** (as in IL): considering pure assertions,
  $[x{=}0]\,x{:=}1\,[x{=}1]$ and $[x{=}1]\,x{:=}1\,[x{=}1]$ would give
  $[\text{false}]\,x{:=}1\,[x{=}1]$, invalid.

## 6. Pros / cons / use cases
- **Pros:** local + compositional **bug-catching**; **no false positives**; captures
  memory-safety bugs; sound **and** complete (footprint) thanks to $x\not\mapsto$.
- **Cons:** being **forward**, it does not pinpoint the *source* inputs (that is
  [SepSIL](07-separation-sufficient-incorrectness-logic.md)); needs the $\not\mapsto$
  machinery for a sound frame.
- **Use cases:** scalable memory-bug detection (Pulse); begin-anywhere symbolic execution.

---

## 📋 Cheatsheet (complete)

### New assertion + satisfaction
$$P ::= \dots\mid\mathsf{emp}\mid a_1\mapsto a_2\mid P_1\ast P_2\mid \boxed{x\not\mapsto}\qquad \langle s,h\rangle\models x\not\mapsto\iff\mathrm{dom}(h)=\{s(x)\}\wedge h(s(x))=\bot.$$
Notable: $x\mapsto v\ast x\not\mapsto\equiv\text{false}$, and $y\mapsto v\ast x\not\mapsto\equiv y\mapsto v\ast x\not\mapsto\wedge\,x{\neq}y$.

### Validity + frame
$$[P]\,c\,[\varepsilon:Q]\ \text{valid}\iff Q\subseteq\llbracket c\rrbracket_\varepsilon P,\qquad \dfrac{[P]\,c\,[\varepsilon:Q]}{[P\ast R]\,c\,[\varepsilon:Q\ast R]}\ [\textsf{frame}]\ (\mathrm{Mod}(c)\cap\mathrm{FV}(R)=\varnothing).$$

### Local axioms (with exit conditions)
$$\dfrac{}{[x\mapsto v]\ [x]:=y\ [ok:x\mapsto y]}\ [\textsf{write}] \qquad \dfrac{}{[x{=}\mathsf{nil}]\ [x]:=y\ [er:x{=}\mathsf{nil}]}\ [\textsf{write-null}]$$
$$\dfrac{}{[y\mapsto v]\ x:=[y]\ [ok:x{=}v\wedge y\mapsto v]}\ [\textsf{read}] \qquad \dfrac{}{[y{=}\mathsf{nil}]\ x:=[y]\ [er:y{=}\mathsf{nil}]}\ [\textsf{read-null}]$$
$$\dfrac{}{[x\doteq x']\ x:=\mathsf{alloc}()\ [ok:x\mapsto\_]}\ [\textsf{alloc}] \qquad \dfrac{}{[x\mapsto v]\ \mathsf{free}(x)\ [ok:x\not\mapsto]}\ [\textsf{free}] \qquad \dfrac{}{[x{=}\mathsf{nil}]\ \mathsf{free}(x)\ [er:x{=}\mathsf{nil}]}\ [\textsf{free-null}]$$

### Error axioms on deallocated cells (the memory bugs)
$$\dfrac{}{[x\not\mapsto]\ [x]:=y\ [er:x\not\mapsto]}\ \text{(use-after-free)} \qquad \dfrac{}{[y\not\mapsto]\ x:=[y]\ [er:y\not\mapsto]}\ \text{(use-after-free)} \qquad \dfrac{}{[x\not\mapsto]\ \mathsf{free}(x)\ [er:x\not\mapsto]}\ \text{(double free)}$$
$$\dfrac{}{[y\not\mapsto]\ x:=\mathsf{alloc}()\ [ok:x\mapsto v\wedge x{=}y]}\ \text{(reuse of a freed address)}$$

### Why the fix works (frame + completeness)
$$\underbrace{[x\mapsto v]\,\mathsf{free}(x)\,[ok:\mathsf{emp}]}_{\text{SL-style: loses the cell}}\ \xrightarrow{\ \text{frame}\ }\ [\text{false}]\,\mathsf{free}(x)\,[ok:x\mapsto v]\ \text{(unsound!)}$$
$$\underbrace{[x\mapsto v]\,\mathsf{free}(x)\,[ok:x\not\mapsto]}_{\text{ISL: keeps the (dead) cell}}\ \Rightarrow\ \text{monotonic heap}\ \Rightarrow\ \text{sound frame + footprint (completeness).}$$

### Theorems
- **[Soundness]** $\vdash[P]\,c\,[\varepsilon:Q]\Rightarrow Q\subseteq\llbracket c\rrbracket_\varepsilon P$.
- **[Footprint / completeness]** any valid ISL triple $[\sigma_P]\,c\,[\varepsilon:\sigma_Q]$ is derivable.
- **[$\ast\textsf{conj}$ unsound]**; **[no-false-positives]** every derivable $er$ triple is a real bug.

### Consequence direction
Weaken the presumption, strengthen/shrink the result (as in IL). Local axioms must be **precise**.
