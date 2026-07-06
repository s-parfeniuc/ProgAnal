---
title: Separation Logic (SL)
abbrev: SL
lectures: "09 (Separation Logic)"
paper: "J. Reynolds; P. O'Hearn, J. Reynolds, H. Yang — Local Reasoning about Programs that Alter Data Structures, CSL 2001"
quadrant: "forward · over-approximation · heap/local"
oneliner: "Hoare Logic for the heap: reason locally about the cells a program actually touches, framing off the rest."
render: "Notation is LaTeX math ($…$ / $$…$$). Preview with a KaTeX markdown extension."
---

# Separation Logic (SL)

**Quadrant:** forward · over-approximation, extended to the **heap** with **local reasoning**.

## 1. Purpose & core idea
SL extends [HL](01-hoare-logic.md) to programs with **pointers and dynamic memory**. Its
signature achievement is **local reasoning**: *"reasoning and specification confined to the
cells a program actually accesses; every other cell automatically stays unchanged."* This
tames aliasing and makes proofs **compositional and scalable**. It is still a
**correctness / over-approximation** logic — it proves absence of bugs.

## 2. Basic definition
A state is now $\sigma=\langle s,h\rangle$: a **store** $s:X\to\mathbb Z$
(variables→values) and a **heap** $h:\mathbb N\rightharpoonup\mathbb Z_\bot$
(locations→values, a *partial* function). Assertions add three connectives:
- $a_1\mapsto a_2$ — the heap is **exactly one cell** at $a_1$ holding $a_2$ (**ownership**).
- $\mathsf{emp}$ — the empty heap.
- $P_1\ast P_2$ — **separating conjunction**: the heap **splits into two disjoint parts**,
  one satisfying $P_1$, the other $P_2$.

The triple $\{P\}\,c\,\{Q\}$ keeps its HL meaning ($\llbracket c\rrbracket P\subseteq Q$),
now over heap-states. **Why $\ast$:** to say $x,y,z$ point to distinct cells, classical
$\wedge$ needs all the pairwise $\neq$ disequations ($O(n^2)$); with $\ast$,
$x\mapsto 1\ast y\mapsto 2\ast z\mapsto 3$ says it **for free** — disjointness is built in.

## 3. Over/under-approximation & information propagation
**Forward, over-approximation — but *local*.** You reason on the **small footprint** (only
the touched cells) with the strongest post, and **frame** the untouched heap through
unchanged. Propagation = local axiom on the footprint, then $\ast R$ for the idle cells.

## 4. Peculiarities & differences vs siblings
- **SL = local (small) axioms + the frame rule.** Each atomic axiom mentions only the
  cells it accesses; the frame rule adds back the rest.
- **Frame rule** $\{P\}\,c\,\{Q\}\Rightarrow\{P\ast R\}\,c\,\{Q\ast R\}$ (side condition:
  $c$'s modified variables disjoint from $R$'s free variables). This is the $\ast$
  generalisation of the $\wedge$-frame seen in IL.
- **Inductive predicates** describe unbounded structures, e.g. list segments
  $\mathsf{ls}$, $\mathsf{list}$; $\ast$ expresses that sublists occupy *disjoint* heap.
- Sibling logics reuse this heap machinery: [ISL](06-incorrectness-separation-logic.md)
  $=$ IL$+$SL, [SepSIL](07-separation-sufficient-incorrectness-logic.md) $=$ SIL$+$SL.

## 5. Properties: soundness & completeness (with *why*)
- **Sound** (by induction on the derivation).
- **Incomplete** — the **footprint property fails**, due to **information loss**.
  **Why:** $\mathsf{free}(x)$ yields $\{\mathsf{emp}\}$, *forgetting that $x$ held a
  location*, so after $x:=\mathsf{alloc}();\mathsf{free}(x)$ you cannot derive facts like
  $y\neq x$. Resources can grow, but SL lets them silently **shrink**, and that lost
  information cannot be recovered. (This is *exactly* the gap that
  [ISL](06-incorrectness-separation-logic.md)'s $x\not\mapsto$ predicate closes.)

## 6. Pros / cons / use cases
- **Pros:** **compositional / scalable** local reasoning for heap code; elegant proofs of
  data-structure surgery (list reversal, concatenation) via inductive predicates.
- **Cons:** incomplete (footprint); still over-approximate ⇒ **false positives** if used
  for bug-finding; classic SL cannot express *deallocated* cells.
- **Use cases:** verification of pointer / dynamic-memory programs; substrate for the
  memory bug logics ISL and SepSIL.

---

## 📋 Cheatsheet (complete)

### State model
$$\sigma=\langle s,h\rangle,\qquad s:X\to\mathbb Z\ \text{(store)},\qquad h:\mathbb N\rightharpoonup\mathbb Z_\bot\ \text{(heap)},\qquad \text{concrete domain }\wp(\Sigma).$$
Disjointness $h_1\mathrel{\#}h_2\triangleq\mathrm{dom}(h_1)\cap\mathrm{dom}(h_2)=\varnothing$; disjoint union $h_1\bullet h_2$ (undefined unless $h_1\mathrel{\#}h_2$).

### Assertion language
$$P ::= \text{(pure: } a_1{<}a_2\mid a_1{=}a_2\mid\neg P\mid P_1\wedge P_2\mid\exists x.P\mid\dots\text{)}\ \mid\ \mathsf{emp}\ \mid\ a_1\mapsto a_2\ \mid\ P_1\ast P_2.$$

### Satisfaction (structural)
$$\langle s,h\rangle\models a_1\mapsto a_2\iff\mathrm{dom}(h)=\{\llbracket a_1\rrbracket s\}\ \wedge\ h(\llbracket a_1\rrbracket s)=\llbracket a_2\rrbracket s$$
$$\langle s,h\rangle\models\mathsf{emp}\iff h=[\,]\qquad\qquad \langle s,h\rangle\models P_1\ast P_2\iff\exists h_1,h_2.\ h=h_1\bullet h_2\wedge\langle s,h_1\rangle\models P_1\wedge\langle s,h_2\rangle\models P_2$$
($\ast$ **splits the heap but not the store**.)

### Heap commands
$$c ::= \dots\mid x:=[a]\ \text{(read)}\ \mid\ [a_1]:=a_2\ \text{(write)}\ \mid\ x:=\mathsf{alloc}()\ \mid\ \mathsf{free}(x)$$

### Local (small) axioms
$$\dfrac{}{\{a\mapsto\_\}\ [a]:=v\ \{a\mapsto v\}}\ [\textsf{write}] \qquad \dfrac{}{\{a\mapsto v\}\ x:=[a]\ \{x{=}v\wedge a\mapsto v\}}\ [\textsf{read}]$$
$$\dfrac{}{\{\mathsf{emp}\}\ x:=\mathsf{alloc}()\ \{x\mapsto\_\}}\ [\textsf{alloc}] \qquad \dfrac{}{\{a\mapsto\_\}\ \mathsf{free}(a)\ \{\mathsf{emp}\}}\ [\textsf{dispose}]$$

### Frame rule (the heart of local reasoning)
$$\dfrac{\{P\}\,c\,\{Q\}}{\{P\ast R\}\,c\,\{Q\ast R\}}\ [\textsf{frame}]\qquad \text{side condition } \mathrm{Mod}(c)\cap\mathrm{FV}(R)=\varnothing.$$

### Useful (in)equivalences
$$P\ast\mathsf{emp}\equiv P,\qquad x\mapsto v\ast x\mapsto w\equiv\text{false},\qquad x\mapsto v\ast y\mapsto w\ \not\Rightarrow\ x\mapsto v.$$

### Inductive predicates (example)
$$\mathsf{ls}(a_1,a_2)\triangleq(a_1{=}a_2\wedge\mathsf{emp})\vee(a_1{\neq}a_2\wedge\exists l.\ a_1\mapsto l\ast\mathsf{ls}(l,a_2)),\qquad \mathsf{list}(a)\triangleq\mathsf{ls}(a,\mathsf{nil}).$$

### Theorems
- **[Soundness]** $\vdash\{P\}\,c\,\{Q\}\Rightarrow\llbracket c\rrbracket P\subseteq Q$.
- **[Incompleteness]** footprint fails: e.g. $\{y\mapsto\_\}\ x{:=}\mathsf{alloc}();\mathsf{free}(x)\ \{y\mapsto\_\wedge y{\neq}x\}$ is valid but not derivable (info loss at $\mathsf{free}$).

### Consequence direction
As in HL: strengthen the precondition, weaken the postcondition.
