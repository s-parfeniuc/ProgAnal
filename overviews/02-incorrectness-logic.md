---
title: Incorrectness Logic (IL)
abbrev: IL
lectures: "05 (Incorrectness Logic), 06 (The Real IL), 07 (More about IL)"
paper: "P. O'Hearn, Incorrectness Logic, POPL 2020"
quadrant: "forward · under-approximation"
oneliner: "Prove the presence of real bugs with no false positives — every result state is genuinely reachable."
render: "Notation is LaTeX math ($…$ / $$…$$). Preview with a KaTeX markdown extension."
---

# Incorrectness Logic (IL)

**Quadrant:** forward · under-approximation ⟶ proves the **presence** of bugs.

## 1. Purpose & core idea
IL is O'Hearn's deliberate **dual of [HL](01-hoare-logic.md)**: "the other side of the
coin." Where HL proves a program is correct, IL proves it is **incorrect** — that a bug
is genuinely reachable — and does so with **no false positives**. This matches how
programmers and bug-finders actually work: reasoning about what *can go wrong*. It is the
theory behind industrial tools (Meta's Infer / Pulse).

## 2. Basic definition
An **incorrectness triple** (O'Hearn calls $P$ the *presumption*, $Q$ the *result*):

$$[P]\,c\,[Q]\ \text{ valid}\quad\overset{\triangle}{\iff}\quad [\![  c ]\!] P \supseteq Q \quad\iff\quad \forall\delta\in Q.\ \exists\sigma\in P.\ \delta\in[\![  c ]\!]\sigma.$$

Read it as: *every state in the result $Q$ is genuinely reachable* by running $c$ from
**some** presumption state. So if $Q$ describes an error and the triple is derivable, the
error is **real**. Compare HL's $\forall\sigma\forall\delta$ (every reachable state
satisfies $Q$) with IL's $\forall\delta\exists\sigma$ (every $Q$-state is reachable).

**The "real IL" (lect. 06)** tags the exit condition:
$$[P]\,c\,[\varepsilon:Q],\qquad \varepsilon\in\{ok,er\},\qquad Q\subseteq[\![  c ]\!]_\varepsilon P.$$
$ok$ = normal termination, $er$ = **erroneous** termination (a crash). The $er$ channel is
what makes IL *find* bugs: it under-approximates the reachable **crash** states.

## 3. Over/under-approximation & information propagation
IL is **forward** and **under-approximating**: $Q$ is a **subset** of the reachable
states — you carry only genuinely-reachable states forward. You may **drop paths** and
only need **finite loop unrolling** (no invariants), because reachability is existential:
a single finite path is a valid witness.

**Slogan (IL side of the duality):** *you must remember information along a path, but you
may forget some paths.*

**Propagation with $ok$/$er$ (the bug-finding engine).** $ok$ carries you **forward along
the good prefix** to the crash site; $er$ **collects the reachable crash states**.
Sequencing short-circuits errors:
$$[\![  c_1;c_2 ]\!]_{er}=\underbrace{[\![  c_1 ]\!]_{er}}_{c_1\ \text{crashes}}\ \cup\ \underbrace{([\![  c_2 ]\!]_{er}\circ[\![  c_1 ]\!]_{ok})}_{c_1\ ok,\ \text{then }c_2\ \text{crashes}}.$$
A non-$\text{false}$ $er$ result is a **proof that a real bug is reachable**.

> [!example] Loop unrolling to find a bug (no invariant)
> Unroll to reach a target value, then guard it:
> $[x{=}0]\ (x{:=}x{+}1)^\star\ [x{=}0]$ (iter0) · $[x{=}0]\ (x{:=}x{+}1)^\star\ [x{=}1]$ (unroll once) · … · $[x{=}0]\ (x{:=}x{+}1)^\star\ [x{=}2^{42}]$.
> Now place a check: $(x{:=}x{+}1)^\star;\ \mathsf{if}\ (x{=}2^{42})\ \mathsf{then}\ \mathsf{error}()$. The derived triple **proves the error is reachable** — a real bug. Reachability needs only *one* finite path per result state; no invariant needed. Combine with $[\textsf{choiceL/R}]$ (drop paths) and $[\textsf{cons}]$ (shrink the post) to isolate the single crashing execution.

> [!example] $ok$/$er$ propagation (short-circuiting)
> $[y{=}v]\ \mathsf{error}();\,x{:=}y\ [er:y{=}v]$ — $\mathsf{error}()$ fails first; $x{:=}y$ never runs.
> $[y{=}v]\ x{:=}y;\,\mathsf{error}()\ [er:x{=}y{=}v]$ — $x{:=}y$ succeeds ($ok$, now $x{=}y{=}v$), *then* $\mathsf{error}()$ carries that state into $er$.
> Division by zero (via $\mathsf{def}$): $[y{=}100x]\ \mathsf{if}\ (y/x{\ge}10)\ \mathsf{then}\ y{:=}y{-}x\ \mathsf{else}\ y{:=}x\ [er:y{=}x{=}0]$ — when $x{=}0$ the guard divides by zero, proving the div-by-zero reachable from $y{=}x{=}0$.

## 4. Peculiarities & differences vs siblings
- **Reversed consequence.** You may **weaken the presumption** and **strengthen/shrink
  the result** — the mirror of HL. Crucially, the **result cannot be weakened** (enlarging
  $Q$ could claim unreachable states, breaking $[\![  c ]\!] P\supseteq Q$). The
  *presumption* can be weakened.
- **Floyd's forward assignment axiom is sound; Hoare's backward axiom is *unsound*** for IL
  (its post could name unreachable states, e.g. $[y{=}42]\,x{:=}42\,[y{=}x]$ "reaches" the
  unreachable $[x{\mapsto}3,y{\mapsto}3]$).
- **No invariants** — loops handled by finite **unrolling**.
- **$[\textsf{conj}]$ is unsound**; $[\textsf{disj}]$ is sound.
- **Frame & ghost variables (compositionality).** The $\wedge$-frame
  $[P]\,c\,[Q]\Rightarrow[P\wedge R]\,c\,[Q\wedge R]$ (when $R$'s free variables are not
  modified by $c$) carries untouched facts through; **ghost / logical variables** (never
  assigned by the program, hence automatically framed) relate pre- and post-state across a
  call. This is the precursor to SL's $\ast$-frame ([SL](05-separation-logic.md)).
- **Bridges to HL:** *agreement* and *denial* let an IL derivation **refute** an HL spec.

## 5. Properties: soundness & completeness (with *why*)
- **Soundness** — every derivable triple is valid. **Why:** induction on the derivation;
  each rule preserves $[\![  c ]\!] P\supseteq Q$ (e.g. $[\textsf{seq}]$:
  $[\![  c_1;c_2 ]\!] P=[\![  c_2 ]\!]([\![  c_1 ]\!] P)\supseteq[\![  c_2 ]\!] R\supseteq Q$).
- **(Relative) completeness** — every valid triple is derivable (given an implication
  oracle). **Why it is *cleaner* than HL's:** assertions are just **sets of states** and
  implication is **set inclusion**, so the finiteness / Gödel obstructions that make HL
  only *relatively* complete do not bite in the same way. Key lemma: $[P]\,c\,[[\![  c ]\!] P]$
  is derivable for every $c,P$; then $[\textsf{cons}]$ shrinks the post to any valid $Q$.

## 6. Pros / cons / use cases
- **Pros:** no false positives ("true-positive theorem"); no invariants; fast,
  **compositional**; the $er$ channel pinpoints reachable crashes.
- **Cons:** by design may **miss** bugs (under-approx); being **forward**, it records path/
  error conditions in the *result*, so it **cannot pinpoint which inputs are responsible**
  (that is [SIL](04-sufficient-incorrectness-logic.md)); results cannot be weakened.
- **Use cases:** industrial bug-finding (Infer / Pulse); reasoning about the presence of bugs.

---

## 📋 Cheatsheet (complete)

### Language
$$c ::= e \mid c_1;c_2 \mid c_1+c_2 \mid c^\star \mid \mathsf{error}() \mid x:=\mathsf{nondet}() \qquad e ::= \mathsf{skip}\mid x:=a\mid b?$$
with $\mathsf{if}\ b\ \mathsf{then}\ c_1\ \mathsf{else}\ c_2\triangleq(b?;c_1)+(\neg b?;c_2)$, $\mathsf{while}\ b\ \mathsf{do}\ c\triangleq(b?;c)^\star;\neg b?$.

### Validity
$$[P]\,c\,[Q]\ \text{valid}\iff[\![  c ]\!] P\supseteq Q\iff\forall\delta\in Q.\ \exists\sigma\in P.\ \delta\in[\![  c ]\!]\sigma. \qquad [P]\,c\,[\varepsilon:Q]\ \text{valid}\iff Q\subseteq[\![  c ]\!]_\varepsilon P.$$

### Relational semantics with exit conditions ($\varepsilon\in\{ok,er\}$)
$$[\![ \mathsf{skip} ]\!]_{ok}=\{(\sigma,\sigma)\},\quad [\![  b? ]\!]_{ok}=\{(\sigma,\sigma)\mid\sigma\models b\},\quad [\![  x:=a ]\!]_{ok}=\{(\sigma,\sigma[[\![  a ]\!]\sigma/x])\}$$
$$[\![ \mathsf{error}() ]\!]_{ok}=\varnothing,\qquad [\![ \mathsf{error}() ]\!]_{er}=\{(\sigma,\sigma)\},\qquad (\text{normal commands have }[\![ \cdot ]\!]_{er}=\varnothing)$$
$$[\![  c_1;c_2 ]\!]_{ok}=[\![  c_2 ]\!]_{ok}\circ[\![  c_1 ]\!]_{ok},\qquad [\![  c_1;c_2 ]\!]_{er}=[\![  c_1 ]\!]_{er}\cup([\![  c_2 ]\!]_{er}\circ[\![  c_1 ]\!]_{ok})$$
**Definedness** (partial exprs, e.g. division): $\mathsf{def}(a_1/a_2)\triangleq\mathsf{def}(a_1)\wedge\mathsf{def}(a_2)\wedge a_2\neq 0$.

### Axioms & inference rules (single-exit form; add $ok:$/$er:$ analogously)

$$\dfrac{}{[P]\ x:=a\ [\exists x'.\,P[x'/x]\wedge x=a[x'/x]]}\ [\textsf{Floyd}] \qquad \dfrac{}{[P]\ \mathsf{skip}\ [P]}\ [\textsf{skip}] \qquad \dfrac{}{[P]\ b?\ [P\wedge b]}\ [\textsf{assume}]$$

$$\dfrac{}{[P]\ x:=\mathsf{nondet}()\ [\exists x.\,P]}\ [\textsf{nondet}] \qquad \dfrac{}{[P]\ \mathsf{error}()\ [ok:\text{false}][er:P]}\ [\textsf{error}]$$

$$\dfrac{[P]\,c_1\,[ok:R]\quad [R]\,c_2\,[\varepsilon:Q]}{[P]\ c_1;c_2\ [\varepsilon:Q]}\ [\textsf{seq}] \qquad \dfrac{[P]\,c_1\,[er:Q]}{[P]\ c_1;c_2\ [er:Q]}\ [\textsf{seq-sc}]$$

$$\dfrac{P'\Rightarrow P\quad [P']\,c\,[Q']\quad Q\Rightarrow Q'}{[P]\,c\,[Q]}\ [\textsf{cons}] \qquad \dfrac{[P]\,c_1\,[Q_1]\quad [P]\,c_2\,[Q_2]}{[P]\ c_1+c_2\ [Q_1\vee Q_2]}\ [\textsf{choice}] \qquad \dfrac{[P]\,c_i\,[Q]}{[P]\ c_1+c_2\ [Q]}\ [\textsf{choiceL/R}]$$

$$\dfrac{}{[P]\ c^\star\ [P]}\ [\textsf{iter0}] \qquad \dfrac{[P]\ c;c^\star\ [Q]}{[P]\ c^\star\ [Q]}\ [\textsf{unroll}] \qquad \dfrac{\forall n\in\mathbb N.\ [P_n]\,c\,[P_{n+1}]}{[P_0]\ c^\star\ [\exists k.\,P_k]}\ [\textsf{iter}]$$

$$\dfrac{[P]\,c\,[Q]}{[P\wedge R]\,c\,[Q\wedge R]}\ [\textsf{frame}]\ (\mathrm{Mod}(c)\cap\mathrm{FV}(R)=\varnothing) \qquad \dfrac{[P_1]\,c\,[Q_1]\quad [P_2]\,c\,[Q_2]}{[P_1\vee P_2]\,c\,[Q_1\vee Q_2]}\ [\textsf{disj}]$$

### Theorems
- **[Soundness]** $\vdash[P]\,c\,[Q]\Rightarrow[\![  c ]\!] P\supseteq Q$.
- **[Relative completeness]** valid $\Rightarrow$ derivable (via lemma $[P]\,c\,[[\![  c ]\!] P]$ + $[\textsf{cons}]$); cleaner than HL (sets + inclusion).
- **[Agreement]** if $[P']\,c\,[Q']$, $P'\Rightarrow P$, and $\{P\}\,c\,\{Q\}$, then $Q'\Rightarrow Q$.
- **[Denial]** (contrapositive) if $[P']\,c\,[Q']$, $P'\Rightarrow P$, and $\neg(Q'\Rightarrow Q)$, then $\neg(\{P\}\,c\,\{Q\})$ — an IL proof refutes an HL spec.
- **[$\textsf{conj}$ unsound]** counterexample $c\triangleq x:=7$, $P_1\equiv x{=}0$, $P_2\equiv x{=}1$, $Q_i\equiv x{=}7$: premises valid but $[\text{false}]\,x{:=}7\,[ok:x{=}7]$ invalid.

### Consequence direction
Weaken the presumption ($P'\Rightarrow P$), **strengthen/shrink** the result ($Q\Rightarrow Q'$). The result is **never** weakened.
