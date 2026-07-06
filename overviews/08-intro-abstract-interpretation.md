---
title: Introduction to Abstract Interpretation
abbrev: AI (intro)
lectures: "11 (Intro AI — basic), 12 (Intro AI — formal)"
paper: "P. Cousot & R. Cousot, POPL 1977; A. Miné, Tutorial on Static Inference of Numeric Invariants (reading)"
theme: "abstraction · over-approximation · sound-but-incomplete static analysis"
oneliner: "Compute a sound over-approximation of a program's behaviour by running it on an abstract domain instead of exact states."
render: "Notation is LaTeX math ($…$ / $$…$$). Preview with a KaTeX markdown extension."
---

# Introduction to Abstract Interpretation

**Theme:** the general framework for **sound-by-construction** static analysis —
over-approximate the (uncomputable) exact behaviour by computing in a simpler
**abstract domain**. Part I of the AI block; the machinery is developed in
[09 order theory & Galois connections](09-order-theory-galois-connections.md),
[10 abstract domains & operators](10-abstract-domains-operators.md), and
[11 abstract analysis (fixpoints, widening)](11-abstract-analysis-fixpoints-widening.md).

## 1. Purpose & core idea
A program has, in general, **infinitely many** executions, and by **Rice's theorem**
every non-trivial semantic property is **undecidable** — so we cannot compute the exact
set of reachable states. Abstract Interpretation (Cousot & Cousot, POPL 1977) makes the
problem tractable by **replacing exact sets of states with abstract properties** and
computing with those. The guiding equation:

$$\textbf{abstraction} \neq \textbf{omission}.$$

We do not *throw away* executions; we describe them by a chosen **property** (e.g. "$x$ is
positive", "$x\in[1,4]$") that is guaranteed to **cover** all of them. The result is a
**sound over-approximation**: it may be imprecise, but it never misses a real behaviour.

## 2. Basic definitions
- **Concrete domain** $C$ — the exact information, typically $\wp(\Sigma)$ (sets of program
  states), ordered by $\subseteq$. See [[denotational-semantics]].
- **Abstract element / abstract domain** — an **abstract element** is a logical property of
  states; the set of them is the **abstract domain** $A$, ordered by a precision order
  $\sqsubseteq$ (lower = more precise).
- **Concretization** $\gamma:A\to C$ — $\gamma(a)$ is the **set of states that satisfy $a$**
  (its meaning). E.g. $\gamma(\mathit{even})=\{0,2,4,\dots\}$.
- **Abstraction** $\alpha:C\to A$ — maps a set of states to the abstract element describing
  it (developed formally in [09](09-order-theory-galois-connections.md)).

## 3. Over-approximation & the soundness principle
An abstract element $a$ **over-approximates** a set $S$ when $S\subseteq\gamma(a)$: every
concrete state is covered. An analysis lifts this to whole programs. The **analysis
function** takes a program $p$ and an abstract pre-state $a$ and returns an abstract
post-state, written $\llbracket p\rrbracket^\sharp a$ (or $\mathrm{analysis}(p,a)$).

> [!important] The soundness square (the one picture to remember)
> *Abstracting then running (abstractly) must cover running then abstracting.* For every
> concrete step $\sigma\xrightarrow{p}\sigma'$ and every abstract $a$ with $\sigma\in\gamma(a)$:
> $$\sigma'\in\gamma\big(\llbracket p\rrbracket^\sharp a\big),\qquad\text{i.e.}\qquad \llbracket p\rrbracket\big(\gamma(a)\big)\ \subseteq\ \gamma\big(\llbracket p\rrbracket^\sharp a\big).$$
> Concrete run **under** abstract run. This is what guarantees no reachable state escapes the analysis.

**Compositionality.** A sound analysis of $p$ is built from sound abstract semantics of its
components — so soundness is proved once per language construct and composes.

**Analysis goal — safety.** Given an **error zone** $E$, compute an over-approximation
$\gamma(a)$ of the reachable states and check $\gamma(a)\cap E=\varnothing$. If it holds,
the program is **provably safe**; if not, the alarm may be spurious (imprecision).

## 4. The numeric domains at a glance (& best abstraction)
The chosen abstract domain trades **precision** for **cost**:

| Domain | Abstract element | Relational? | Expressiveness |
|---|---|---|---|
| **Signs** | sign of each variable ($x\le 0$, $x\ge 0$, …) | no | coarsest |
| **Intervals** | $[\min,\max]$ per variable, $\min,\max\in\mathbb Z\cup\{-\infty,+\infty\}$ | no | $\supset$ Signs |
| **Octagons** | $\pm x\pm y\le c$ | yes (weakly) | $\supset$ Intervals |
| **Convex polyhedra** | conjunctions of linear inequalities $c_1x+c_2y\le c$ | yes | $\supset$ Octagons |
| **Congruences** | $x\equiv b \ (\mathrm{mod}\ a)$ | no | orthogonal |

**Non-relational** (Signs, Intervals) track each variable independently; **relational**
(Octagons, Polyhedra) capture links between variables (e.g. $x\le y$).

**Best abstraction.** $a$ is the *best* (most precise) over-approximation of $S$ iff
(1) $S\subseteq\gamma(a)$ and (2) any other over-approximation is coarser:
$S\subseteq\gamma(b)\Rightarrow\gamma(a)\subseteq\gamma(b)$. A best abstraction **need not
exist** (e.g. a disk has no smallest enclosing convex polyhedron) or may be too expensive —
then we use an abstraction *as precise as practical*, not necessarily the best. (When it
exists it is $\gamma(\alpha(S))$ — see [09](09-order-theory-galois-connections.md).)

## 5. Properties: soundness vs precision (why sound-but-incomplete)
- **Soundness (never lie about safety).** By Rice/undecidability we cannot be exact, so we
  choose to be **sound**: *if the analysis says "safe/YES", the property truly holds*;
  otherwise the answer is **"don't know"**. An analysis that can answer "safe" when it isn't
  (a **false negative**) is **unsound** and worthless for verification.
- **Incompleteness (false alarms).** Over-approximation means the analysis may report a
  **false positive** — flag a state that is not actually reachable. More precise domains
  reduce false alarms at higher cost.
- This is the deliberate opposite of the under-approximation logics ([IL](02-incorrectness-logic.md)/[SIL](04-sufficient-incorrectness-logic.md)),
  which are complete-for-bugs (no false positives) but may miss bugs. AI is the
  **over-approximation** stance: sound for proving **absence** of bugs.

## 6. Pros / cons / use cases
- **Pros:** **sound by construction**; fully **automatic** (no annotations/invariants);
  **tunable** precision/cost via the domain; compositional and scalable.
- **Cons:** **false alarms** (incompleteness); designing precise+cheap domains and ensuring
  **termination** of the fixpoint (needs [widening](11-abstract-analysis-fixpoints-widening.md)) is the real work.
- **Use cases:** industrial static analysers — Astrée (proved absence of runtime errors in
  Airbus flight-control code), Infer, Polyspace; numeric-invariant inference; verifying
  memory safety, absence of overflow/div-by-zero, array-bounds.

---

## 📋 Cheatsheet (complete)

### The AI recipe
$$\underbrace{\wp(\Sigma)}_{\text{concrete } C}\ \xrightleftharpoons[\ \gamma\ ]{\ \alpha\ }\ \underbrace{A}_{\text{abstract}} \qquad\text{compute in } A,\ \text{read back with } \gamma.$$

### Key objects
$$\text{concrete domain } (C,\subseteq)=(\wp(\Sigma),\subseteq);\quad \text{abstract domain } (A,\sqsubseteq);\quad \gamma:A\to C\ (\text{meaning});\quad \alpha:C\to A\ (\text{best descriptor}).$$
$$a\ \text{over-approximates}\ S \iff S\subseteq\gamma(a).$$

### Soundness (per step and as an analysis)
$$\llbracket p\rrbracket(\gamma(a))\subseteq\gamma(\llbracket p\rrbracket^\sharp a) \qquad\Longleftrightarrow\qquad \forall\sigma\in\gamma(a).\ \llbracket p\rrbracket\sigma\subseteq\gamma(\mathrm{analysis}(p,a)).$$
Safety check: reachable$(p)\subseteq\gamma(a)$ and $\gamma(a)\cap E=\varnothing\ \Rightarrow\ p$ avoids $E$.

### Best abstraction
$$a=\text{best of } S \iff S\subseteq\gamma(a)\ \wedge\ \big(S\subseteq\gamma(b)\Rightarrow\gamma(a)\subseteq\gamma(b)\big).\qquad \text{When it exists: } a=\alpha(S).$$
Best need not exist / may be too costly (e.g. Convex Polyhedra for a curved region).

### Numeric domains (increasing precision & cost)
$$\text{Signs}\ \subsetneq\ \text{Intervals}\ \subsetneq\ \text{Octagons}\ \subsetneq\ \text{Convex Polyhedra};\qquad \text{Congruences } (x\equiv b\bmod a)\ \text{orthogonal}.$$
Non-relational: Signs, Intervals, Congruences. Relational: Octagons, Polyhedra.

### Soundness vs precision (the two failure modes)
- **Unsound** = **false negatives** (says safe when not) — forbidden.
- **Incomplete** = **false positives / false alarms** (flags a non-reachable state) — tolerated; reduced by more precise domains.
- Analysis verdicts: **YES** ⟹ property holds; **not YES** = **"don't know"** (Rice's theorem forbids a decision procedure).

### Slogans
$$\textbf{abstraction} \neq \textbf{omission};\qquad \text{concrete run } \subseteq \text{ abstract run (via } \gamma);\qquad \text{sound for proving absence of bugs.}$$
