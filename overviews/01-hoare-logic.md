---
title: Hoare Logic (HL)
abbrev: HL
lectures: "03 (Hoare Logic), 04 (Total Correctness and Invariants)"
paper: "C.A.R. Hoare, An Axiomatic Basis for Computer Programming, CACM 1969"
quadrant: "forward · over-approximation"
oneliner: "Prove a program is correct — from a valid precondition, terminating runs land in the postcondition."
render: "Notation is LaTeX math ($…$ / $$…$$). Preview with a KaTeX markdown extension (Markdown Preview Enhanced or Markdown+Math)."
---

# Hoare Logic (HL)

**Quadrant:** forward · over-approximation ⟶ proves the **absence** of bugs.

## 1. Purpose & core idea
Hoare Logic is the original program logic. Its job is **verification**: showing that a
program does what it should. You annotate the code with logical assertions and reduce
"is this correct?" to deriving **triples** with one syntactic rule per language
construct. Every other logic in this course is a variation on HL, so it is the reference
point for all of them.

## 2. Basic definition
A **Hoare triple** $\{P\}\,c\,\{Q\}$ ($P$ = precondition, $Q$ = postcondition) means:

> *Whenever $c$ is executed in a state satisfying $P$, **if** it terminates, the final
> state satisfies $Q$.*

Viewing assertions as **sets of states** and $[\![ c ]\!]$ as the collecting
semantics (a map on sets of states):

$$\{P\}\,c\,\{Q\} \ \text{ valid} \quad\overset{\triangle}{\iff}\quad [\![ c ]\!]  P \subseteq Q \quad\iff\quad \forall\sigma\in P.\ \forall\delta\in[\![ c ]\!] \sigma.\ \delta\in Q.$$

This is **partial correctness**: it says nothing about termination (a diverging $c$ has
$[\![ c ]\!]\sigma = \varnothing \subseteq Q$ trivially). **Total correctness**
$=$ partial correctness $+$ termination, proved by adding a **variant** (a ranking function).

## 3. Over/under-approximation & information propagation
HL is **forward** and **over-approximating**: $Q$ is a **superset** of the states actually
reachable from $P$. You push a (possibly too large) set of states forward through the
program, weakening as needed. Because it over-approximates, HL is sound for proving that
*nothing bad is reachable* — but used naively for bug-finding it can report a **false
positive** (a state in $Q$ that no real execution reaches).

**Slogan (HL side of O'Hearn's duality):** *you may forget information along a path, but
you must remember all the paths* — every branch must re-establish $Q$.
> [!note] Weakening loses precision, never soundness
> The precise forward step is the **strongest postcondition** $sp(c,P)=[\![  c ]\!] P$;
> taking it always loses no information and commands compose exactly,
> $sp(c_2,sp(c_1,P))=[\![  c_1;c_2 ]\!] P$. Weakening (the consequence rule) is
> *optional*. Even after weakening, the assertion $R$ still satisfies
> $\text{reachable}\subseteq R$, so proving $R\cap\mathit{Bad}=\varnothing$ still yields
> $\text{reachable}\cap\mathit{Bad}=\varnothing$ — a **genuine** safety proof. Over-weakening
> only makes $R$ spuriously touch $\mathit{Bad}$, causing a **false alarm** (you fail to
> prove safety), never a wrong "safe" verdict. Contrast [IL](02-incorrectness-logic.md):
> there the *result* must **not** be weakened (a superset could claim unreachable states).


## 4. Peculiarities & differences vs siblings
- **Two assignment axioms, opposite orientations.** *Floyd's* is **forward** (pushes a
  precondition to the strongest post); *Hoare's* is **backward** (pulls a postcondition
  back by substitution). Hoare's backward axiom is the practical one for proofs.
- The **while rule needs a loop invariant** — the creative, hard part of an HL proof
  (McCarthy 91 needs a non-obvious invariant *and* a lexicographic variant).
- Contrast the incorrectness world: HL's $[\![  c ]\!] P\subseteq Q$ becomes
  IL's $\supseteq$ ([IL](02-incorrectness-logic.md)); its backward mirror is
  [NC](03-necessary-conditions.md), via $\{P\}c\{Q\}\iff(\neg P)c(\neg Q)$.

## 5. Properties: soundness & completeness (with *why*)
- **Soundness** — *every derivable triple is valid.* **Why:** induction on the derivation
  tree; each rule preserves $[\![ \cdot ]\!] P\subseteq Q$ (e.g. $[\textsf{seq}]$:
  $[\![  c_1;c_2 ]\!] P=[\![  c_2 ]\!]([\![  c_1 ]\!] P)\subseteq[\![  c_2 ]\!] R\subseteq Q$).
- **Incompleteness (absolute)** — *not* every valid triple is derivable. **Why (two
  independent reasons):**
  1. $\{\text{true}\}\,c\,\{\text{false}\}$ is valid **iff** $c$ diverges on all inputs; the
     derivable triples are recursively enumerable, but non-termination is **not r.e.**
     (halting problem).
  2. $\{\text{true}\}\,\mathsf{skip}\,\{Q\}$ is valid **iff** $Q$ is a tautology; by **Gödel**
     no effective proof system captures all true arithmetic assertions.
- **Relative completeness (Cook)** — *with an oracle deciding implications $P\Rightarrow P'$,
  HL is complete.* **Why:** the obstruction is arithmetic, not the program logic.
  $wlp(c,Q)$ is expressible, $\{wlp(c,Q)\}\,c\,\{Q\}$ is derivable, and $[\textsf{cons}]$
  closes the gap — cleanly separating reasoning about *programs* from reasoning about *arithmetic*.

## 6. Pros / cons / use cases
- **Pros:** the foundation; directly proves correctness (absence of bugs); mature,
  compositional, one rule per construct.
- **Cons:** over-approximation ⇒ **false positives** if repurposed for bug-finding;
  requires human-supplied **invariants/variants**; undecidable/incomplete in general;
  no heap (that is [SL](05-separation-logic.md)).
- **Use cases:** deductive program **verification**; the semantic yardstick for IL/NC/SIL.

---

## 📋 Cheatsheet (complete)

### Language (IMP / regular commands)
$$c ::= x := a \mid \mathsf{skip} \mid c_1;c_2 \mid \mathsf{if}\ b\ \mathsf{then}\ c_1\ \mathsf{else}\ c_2 \mid \mathsf{while}\ b\ \mathsf{do}\ c$$

Regular-command form (lect. 04): $c ::= e \mid c_1;c_2 \mid c_1+c_2 \mid c^\star$, atomic
$e ::= \mathsf{skip}\mid x:=a\mid b?$, with $\mathsf{if}\ b\ \mathsf{then}\ c_1\ \mathsf{else}\ c_2 \triangleq (b?;c_1)+(\neg b?;c_2)$
and $\mathsf{while}\ b\ \mathsf{do}\ c \triangleq (b?;c)^\star;\neg b?$.

### Validity
$$\{P\}\,c\,\{Q\}\ \text{valid} \iff [\![  c ]\!] P\subseteq Q \iff \forall\sigma\in P.\ \forall\delta\in[\![  c ]\!]\sigma.\ \delta\in Q \qquad\text{(partial correctness)}$$

### Axioms & inference rules (partial correctness)

$$\dfrac{}{\{P\}\ \mathsf{skip}\ \{P\}}\ [\textsf{skip}] \qquad\qquad \dfrac{}{\{Q[a/x]\}\ x:=a\ \{Q\}}\ [\textsf{assign-Hoare, bwd}]$$

$$\dfrac{}{\{P\}\ x:=a\ \{\exists x'.\, P[x'/x]\wedge x=a[x'/x]\}}\ [\textsf{assign-Floyd, fwd}]$$

$$\dfrac{\{P\}\,c_1\,\{R\}\qquad \{R\}\,c_2\,\{Q\}}{\{P\}\ c_1;c_2\ \{Q\}}\ [\textsf{seq}] \qquad\qquad \dfrac{\{P\wedge b\}\,c_1\,\{Q\}\qquad \{P\wedge\neg b\}\,c_2\,\{Q\}}{\{P\}\ \mathsf{if}\ b\ \mathsf{then}\ c_1\ \mathsf{else}\ c_2\ \{Q\}}\ [\textsf{if}]$$

$$\dfrac{\{P\wedge b\}\,c\,\{P\}}{\{P\}\ \mathsf{while}\ b\ \mathsf{do}\ c\ \{P\wedge\neg b\}}\ [\textsf{while}] \qquad\qquad \dfrac{P\Rightarrow P'\qquad \{P'\}\,c\,\{Q'\}\qquad Q'\Rightarrow Q}{\{P\}\,c\,\{Q\}}\ [\textsf{cons}]$$

### Total-correctness while rule (lect. 04)
$t$ = variant (ranking function), $z$ = fresh ghost snapshot of $t$:

$$\dfrac{\{P\wedge b\}\,c\,\{P\}\qquad \{P\wedge b\wedge t=z\}\,c\,\{t<z\}\qquad P\Rightarrow t\ge 0}{\{P\}\ \mathsf{while}\ b\ \mathsf{do}\ c\ \{P\wedge\neg b\}}\ [\textsf{while-total}]$$

Obligations: (1) invariant preserved; (2) variant strictly decreases each iteration;
(3) variant bounded below ($t\ge 0$). $\Rightarrow$ termination (well-founded descent).

### Regular-command proof system (minimal, lect. 04)

$$\dfrac{}{\{P\}\,e\,\{[\![  e ]\!] P\}}\ [\textsf{atom}] \qquad \dfrac{\{P\}\,r_1\,\{R\}\quad \{R\}\,r_2\,\{Q\}}{\{P\}\,r_1;r_2\,\{Q\}}\ [\textsf{seq}] \qquad \dfrac{\forall i\in\{1,2\}.\ \{P\}\,r_i\,\{Q\}}{\{P\}\,r_1+r_2\,\{Q\}}\ [\textsf{choice}] \qquad \dfrac{\{P\}\,r\,\{P\}}{\{P\}\,r^\star\,\{P\}}\ [\textsf{iter}]$$

Auxiliary: $[\textsf{disj}]$, $[\textsf{conj}]$, $[\textsf{frame}]$ (side cond. $\mathrm{Mod}(r)\cap\mathrm{FV}(R)=\varnothing$), $[\textsf{stren}]$, $[\textsf{weak}]$.

### Related state transformers (lect. 02 & 04)
$$sp(c,P)=[\![  c ]\!] P \quad\text{(strongest post, forward)}$$
$$wlp(c,Q)\triangleq\{\sigma\mid [\![  c ]\!]\{\sigma\}\subseteq Q\} \quad(\forall,\ \text{liberal — HL's backward precondition})$$
$$wpp(c,Q)\triangleq[\![  c ]\!]^{op}Q=\{\sigma\mid [\![  c ]\!]\sigma\cap Q\neq\varnothing\} \quad(\exists,\ \text{possible — backward})$$

The **weakest possible precondition** $wpp$ is the backward analog of $sp$ and the transformer
behind the backward logics: [NC](03-necessary-conditions.md) bounds $P$ *above* it
($[\![  c ]\!]^{op}Q\subseteq P$), [SIL](04-sufficient-incorrectness-logic.md) bounds
$P$ *below* it ($P\subseteq[\![  c ]\!]^{op}Q$).

**Adjunction (Galois):** $\;P\subseteq wlp(c,Q)\iff[\![  c ]\!] P\subseteq Q.$

### Theorems
- **[Soundness]** $\vdash\{P\}\,c\,\{Q\}\ \Rightarrow\ [\![  c ]\!] P\subseteq Q$. (induction on derivation)
- **[Incompleteness I]** $\{\text{true}\}\,c\,\{\text{false}\}$ valid iff $c$ diverges (halting not r.e.).
- **[Incompleteness II]** $\{\text{true}\}\,\mathsf{skip}\,\{Q\}$ valid iff $Q$ a tautology (Gödel).
- **[Relative completeness / Cook]** with an implication oracle, $[\![  c ]\!] P\subseteq Q\ \Rightarrow\ \vdash\{P\}\,c\,\{Q\}$.

### Consequence direction
Strengthen the precondition ($P\Rightarrow P'$), weaken the postcondition ($Q'\Rightarrow Q$).
