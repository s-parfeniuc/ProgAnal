---
title: Necessary Conditions (NC)
abbrev: NC
lectures: "07 (More about IL and Necessary Conditions)"
paper: "P. Cousot, R. Cousot, M. Fähndrich, F. Logozzo, Automatic Inference of Necessary Preconditions, VMCAI 2013"
quadrant: "backward · over-approximation"
oneliner: "Infer a necessary precondition — one whose violation guarantees the program will fail."
render: "Notation is LaTeX math ($…$ / $$…$$). Preview with a KaTeX markdown extension."
---

# Necessary Conditions (NC)

**Quadrant:** backward · over-approximation ⟶ infers **necessary** preconditions for correctness.

## 1. Purpose & core idea
NC answers: *"under which precondition, if violated, will the program **always** be
incorrect?"* Such a **necessary precondition** is ideal for **automatic inference**:
sufficient preconditions (à la $wlp$) over-burden callers, whereas a necessary condition,
when broken, is an unambiguous alarm — with an extremely low false-positive ratio
(Microsoft's Clousot / Code Contracts). It is the **backward, over-approximating** corner
of the taxonomy, and is essentially [HL](01-hoare-logic.md) read in the contrapositive.

## 2. Basic definition
Taking $Q$ = the set of **good** (acceptable) final states:

$$(P)\,c\,(Q)\ \text{ valid}\quad\overset{\triangle}{\iff}\quad [\![  c ]\!]^{op}Q \subseteq P \quad\iff\quad \forall\delta\in Q.\ \forall\sigma\in[\![  c ]\!]^{op}\delta.\ \sigma\in P.$$

Here $[\![  c ]\!]^{op}Q=\{\sigma\mid[\![  c ]\!]\sigma\cap Q\neq\varnothing\}$ is the
**backward** (pre-image) semantics — exactly the **weakest possible precondition** $wpp$
from lecture 2. Reading: **every** state that can reach a good outcome lies in $P$.
Contrapositive: $\sigma\notin P \Rightarrow$ (ignoring divergence) *every* run from $\sigma$
is bad. So $P$ is a **necessary** condition for correctness.

Trace view: from $\sigma$, executions split into $G$ood (end in $Q$), $B$ad (assertion
violation: div-by-zero, null, overflow…), $I$nfinite. NC says $G(\sigma)\neq\varnothing\Rightarrow\sigma\in P$.

## 3. Over/under-approximation & information propagation
**Backward, over-approximation.** You start from the postcondition $Q$ and pull back a
**superset** of the states that *can* reach it. Being over-approximate, $P$ is sound as a
*necessary* condition: it may include some innocent states, but it never excludes a state
that could be good — so a state outside $P$ is *guaranteed* bad.

## 4. Peculiarities & differences vs siblings
- **NC is HL in the contrapositive.** The tightest (strongest) necessary precondition is
  $wpp(c,Q)=[\![  c ]\!]^{op}Q$, the backward analog of the strongest postcondition.
- **Same consequence direction as [IL](02-incorrectness-logic.md):** weaken the pre,
  strengthen the post.
- **Sufficient vs necessary:** $wlp(c,Q)$ is a *sufficient* precondition (if it holds, no
  bad state is reached, $\sigma\in wlp(c,Q)\Rightarrow B(\sigma)=\varnothing$); NC gives a
  *necessary* one (if it fails, the program is inevitably wrong).

## 5. Properties: soundness & completeness (with *why*)
- The course presents NC **semantically** and via its **HL-duality**, and explicitly notes
  *"there is not a proof system, but…"* — so unlike HL/IL/SIL there is no dedicated
  syntactic calculus developed here. Its metatheory rides on HL: since
  $\{P\}\,c\,\{Q\}\iff(\neg P)\,c\,(\neg Q)$, soundness/completeness statements transfer
  from Hoare Logic under complementation.
- **Why the duality holds:** $[\![  c ]\!] P\subseteq Q$ iff
  $[\![  c ]\!]^{op}(\neg Q)\subseteq\neg P$ (contrapositive of the reachability
  relation), i.e. $\{P\}c\{Q\}\iff(\neg P)c(\neg Q)$.

## 6. Pros / cons / use cases
- **Pros:** necessary preconditions are easy to explain to users, **very low
  false-positive rate**, well suited to *automatic inference*; a good fit for
  contract/precondition tooling.
- **Cons:** it is a correctness-oriented, over-approximate view (does not *prove* a bug);
  no standalone proof system in the course.
- **Use cases:** automatic precondition inference (Clousot); characterising the states
  from which correctness is even *possible*.

---

## 📋 Cheatsheet (complete)

### Backward (converse) semantics
$$[\![  c ]\!]^{op}\delta\triangleq\{\sigma\mid\delta\in[\![  c ]\!]\sigma\},\qquad \sigma\in[\![  c ]\!]^{op}\delta\iff\delta\in[\![  c ]\!]\sigma,\qquad [\![  c ]\!]^{op}Q=\bigcup_{\delta\in Q}[\![  c ]\!]^{op}\delta = wpp(c,Q).$$

### Validity
$$(P)\,c\,(Q)\ \text{valid}\iff[\![  c ]\!]^{op}Q\subseteq P\iff\forall\delta\in Q.\ \forall\sigma\in[\![  c ]\!]^{op}\delta.\ \sigma\in P.$$
Tightest (strongest) valid $P$ is $wpp(c,Q)=[\![  c ]\!]^{op}Q$.

### Consequence rule
$$\dfrac{P'\Rightarrow P\quad (P')\,c\,(Q')\quad Q\Rightarrow Q'}{(P)\,c\,(Q)}\ [\textsf{cons}]$$
Direction: **weaken the pre, strengthen the post** (same as IL).

### Sufficient vs necessary (traces $T=G\cup B\cup I$)
$$\text{sufficient: }\ \sigma\in wlp(c,Q)\Rightarrow B(\sigma)=\varnothing \qquad\qquad \text{necessary (NC): }\ G(\sigma)\neq\varnothing\Rightarrow\sigma\in P.$$

### Theorems / key facts
- **[HL–NC duality]** $\{P\}\,c\,\{Q\}\iff(\neg P)\,c\,(\neg Q)$; equivalently $[\![  c ]\!] P\subseteq Q\iff[\![  c ]\!]^{op}(\neg Q)\subseteq\neg P$.
- **[Weakest/strongest]** HL: given $Q$, find the *weakest* $P$ ($wlp$). NC mirrors it: given $Q$, find the *strongest* $P$ ($wpp$).
- **[Proof system]** none developed in the course — NC is characterised semantically and via the HL duality.

### The taxonomy square (NC is backward · over)
$$\begin{array}{c|c|c} & \textbf{Forward } [\![  c ]\!] P & \textbf{Backward } [\![  c ]\!]^{op}Q\\\hline \textbf{Over}\ (\subseteq) & \text{HL}:\ [\![  c ]\!] P\subseteq Q & \textbf{NC}:\ [\![  c ]\!]^{op}Q\subseteq P\\\hline \textbf{Under}\ (\supseteq) & \text{IL}:\ [\![  c ]\!] P\supseteq Q & \text{SIL}:\ P\subseteq[\![  c ]\!]^{op}Q \end{array}$$
