---
title: 0-CFA — Existence & the Least Solution
abbrev: CFA (least solution)
lectures: "19 (CFA — existence)"
paper: "Nielson, Nielson & Hankin, Principles of Program Analysis, Ch. 3"
theme: "the acceptable solutions form a Moore family, so a best (least) CFA exists; syntax-directed reformulation"
oneliner: "Acceptable analyses are closed under intersection (a Moore family), so every expression has a least = most precise CFA — computable via the syntax-directed specification ⊧ₛ."
render: "Notation is LaTeX math ($…$ / $$…$$). Preview with a KaTeX markdown extension."
---

# 0-CFA — Existence & the Least Solution

**Theme:** the acceptability relation of [13](13-cfa-motivation-0cfa-specification.md) accepts
*many* guesses (including the trivial $\top$). This file shows a **least (most precise) one
always exists** and moves toward *computing* it via a syntax-directed reformulation
(the actual solving is [16](16-0cfa-constraint-based-solving.md)).

## 1. Purpose & core idea
Two questions the specification leaves open: **does every expression have a CFA at all?** and
**is there a best one?** Both answers are **yes** — because the set of acceptable solutions is
a **Moore family** (closed under greatest lower bounds), which automatically has a least
element. Getting there also clarifies *why acceptability must be defined coinductively*, and
yields a more computational specification.

## 2. The lattice of solutions
Order proposed solutions **pointwise** — fewer flows = more precise:
$$(\hat C_1,\hat\rho_1)\sqsubseteq(\hat C_2,\hat\rho_2) \iff \forall l.\ \hat C_1(l)\subseteq\hat C_2(l)\ \wedge\ \forall x.\ \hat\rho_1(x)\subseteq\hat\rho_2(x).$$
**Smaller = more precise.** This makes the set of all proposed solutions a **complete lattice**.

## 3. Existence & the least CFA (Moore family)
> [!important] Moore family ⟹ least solution
> A **Moore family** (a.k.a. **closure system**) is a subset $Y$ of a complete lattice $L$ closed
> under **glbs**: $\sqcap Y'\in Y$ for **every** $Y'\subseteq Y$. It always contains a **least**
> element $\sqcap Y$ and a **greatest** $\top=\sqcap\varnothing$, and is **never empty**.
>
> **Theorem.** For every $ie$, the set $\{(\hat C,\hat\rho)\mid(\hat C,\hat\rho)\models ie\}$ of
> acceptable analyses **is a Moore family** (proof by coinduction on $ie$: if all
> $(\hat C_i,\hat\rho_i)\models ie$ then $\sqcap_i(\hat C_i,\hat\rho_i)\models ie$).
>
> **Corollaries:** (i) taking $Y'=\varnothing$ gives $\top\models ie$ — **every expression admits
> a CFA**; (ii) taking $Y'=$ all acceptable solutions gives $\sqcap Y'\models ie$ — the
> **least (most precise) CFA exists**, and it is below every other acceptable solution.

The callout is the headline; the rest of this section unpacks *why each clause of it is true*,
because the subtleties (the empty-set corollary, the reason it is $\sqcap$ and not $\sqcup$, and
why "least = best") are exactly what makes CFA a well-defined object rather than a heuristic.

### 3.1 What a Moore family really is (and why it is never empty)
Fix the complete lattice of proposed solutions $L=\widehat{\mathit{Cache}}\times\widehat{\mathit{Env}}$
from §2, ordered pointwise. Because each coordinate is a powerset $\wp(\mathit{Term})$ and $L$ is a
pointwise product of such, **all** glbs and lubs exist, computed coordinatewise:
$$\textstyle\big(\sqcap_i(\hat C_i,\hat\rho_i)\big)=\big(\lambda l.\bigcap_i\hat C_i(l),\ \lambda x.\bigcap_i\hat\rho_i(x)\big),\qquad \top=\big(\lambda l.\mathit{Term},\ \lambda x.\mathit{Term}\big).$$
A Moore family $Y\subseteq L$ is a subset that is **closed under taking glbs of arbitrary
sub-collections** — including the two extreme sub-collections:

- $Y'=\varnothing$. The glb of *no* constraints is the **greatest** element: $\sqcap\varnothing=\top$
  (every element of $L$ is vacuously a lower bound of $\varnothing$, and $\top$ is the greatest of
  them). Closure forces $\top\in Y$, so **a Moore family is automatically non-empty and has a top.**
- $Y'=Y$ (the whole family). Closure forces $\sqcap Y\in Y$: the glb of *everything* in $Y$ is
  itself in $Y$, hence is the **least** element of $Y$.

So "Moore family" packs both existence facts into one closure property: a top always sits inside
(nothing to prove — it exists), and a canonical bottom is manufactured by intersecting the whole
set. Note $(Y,\sqsubseteq)$ is then itself a complete lattice, but a *subtle* one: it shares $L$'s
meet, yet its join is $\bigsqcup^Y Z=\sqcap\{y\in Y\mid \forall z\in Z.\ z\sqsubseteq y\}$
(least member of $Y$ above $Z$) — generally **not** $L$'s union. $Y$ is closed under meets, **not**
under joins; that asymmetry is the whole story of §3.2.

### 3.2 Why the acceptable solutions are closed under $\sqcap$ (the actual mechanism)
The clauses of $\models$ (file [13](13-cfa-motivation-0cfa-specification.md)) are all of one shape:
a **conjunction of conditional inclusions**
$$\big(t\in\hat C(l')\big)\ \Rightarrow\ \big(\hat C(l_a)\subseteq\hat\rho(x)\ \wedge\ \hat C(l_b)\subseteq\hat C(l)\big),$$
plus unconditional inclusions like $\hat\rho(x)\subseteq\hat C(l)$ for $[\textsf{var}]$. **Every such
clause is preserved under coordinatewise intersection**, and this is the beating heart of the theorem.
Take the hard case, $[\textsf{app}]$ on $(t_1^{l_1}\,t_2^{l_2})^l$, and suppose
$(\hat C_i,\hat\rho_i)\models ie$ for all $i\in I$. Write $(\hat C,\hat\rho)=\sqcap_i(\hat C_i,\hat\rho_i)$.
Let a closure $\mathsf{fn}\,x\Rightarrow t_0^{l_0}\in\hat C(l_1)=\bigcap_i\hat C_i(l_1)$. Then it lies
in $\hat C_i(l_1)$ for **every** $i$ — this is the crucial step: *membership in the intersection is
the strongest possible antecedent, so it fires the constraint in all copies at once.* Acceptability
of each $(\hat C_i,\hat\rho_i)$ therefore gives, for every $i$,
$$\hat C_i(l_2)\subseteq\hat\rho_i(x)\quad\text{and}\quad\hat C_i(l_0)\subseteq\hat C_i(l).$$
Intersecting over $i$ (intersection is monotone, and $\bigcap_i A_i\subseteq\bigcap_i B_i$ whenever
$A_i\subseteq B_i$ for all $i$):
$$\hat C(l_2)=\textstyle\bigcap_i\hat C_i(l_2)\subseteq\bigcap_i\hat\rho_i(x)=\hat\rho(x),\qquad \hat C(l_0)\subseteq\hat C(l).$$
The recursive obligation $(\hat C,\hat\rho)\models t_0^{l_0}$ is discharged by the **coinductive
hypothesis** (below). All other clauses are easier: $[\textsf{var}]$'s $\hat\rho(x)\subseteq\hat C(l)$
intersects the same way; $[\textsf{con}]$/$[\textsf{op}]$ are unconditionally true.

**Why $\sqcap$ and not $\sqcup$.** Repeat the argument with unions. From
$\mathsf{fn}\,x\Rightarrow t_0\in\bigcup_i\hat C_i(l_1)$ you only learn the closure is in *some*
$\hat C_j(l_1)$, so you only get the consequent from that single $j$ — nothing forces
$\hat C_k(l_2)\subseteq\hat\rho_k(x)$ for the other $k$, and the union of consequents can fail. Hence
**acceptability is preserved by meets but not by joins** — precisely the closure-system asymmetry of
§3.1, and the reason the acceptable set is a Moore family rather than a full sublattice.

**Where coinduction enters.** For non-recursive constructs the above is plain structural induction.
But $[\textsf{app}]$ recursively demands $\models t_0^{l_0}$ for *every* function reachable at the
operator, and with $\mathsf{fun}$ / higher-order recursion the body $t_0$ can loop back to the same
call — the "subterm" relation is not well-founded. So $\models$ is the **greatest fixed point** of
the monotone functional built from these clauses (file [14](14-0cfa-semantic-correctness.md) reads
the closure/agreement relations coinductively for the same reason). The Moore-family proof is
therefore by **coinduction**: to show $\sqcap_i(\hat C_i,\hat\rho_i)\models ie$, exhibit the set
$\{(\sqcap_i(\hat C_i,\hat\rho_i),\,ie)\mid \forall i.\,(\hat C_i,\hat\rho_i)\models ie\}$ and check it
is a **post-fixed point** (closed under one unfolding of the functional) — which is exactly the
clause-by-clause intersection check just done. The gfp then contains it, i.e. the meet is acceptable.

### 3.3 The two corollaries, read out loud
- **(i) $\top\models ie$ — existence.** Instantiating closure at $Y'=\varnothing$ hands us $\top\in Y$
  for free. Concretely $\top=(\lambda l.\mathit{Term},\lambda x.\mathit{Term})$: "**every** program
  point may hold **every** function, and every variable may be bound to every function." Every
  inclusion $\hat C(\cdot)\subseteq\hat\rho(\cdot)$ etc. is trivially satisfied because the right-hand
  side is already the whole universe. So the acceptability relation is **never vacuous** — CFA
  *always* has at least one solution, no matter how tangled the program. This is the analysis-side
  analogue of "the coarsest abstraction is always sound."
- **(ii) $\sqcap Y\models ie$ — the best solution.** Instantiating closure at $Y'=Y$ gives the glb of
  *all* acceptable solutions, and it is itself acceptable. Being the glb, it sits $\sqsubseteq$ every
  other acceptable $(\hat C,\hat\rho)$. This is **the 0-CFA of $e$** — the canonical object that lets
  us speak of "*the* control-flow analysis of a program" rather than "*an* acceptable guess."

### 3.4 Why "least = most precise = best" (and still sound)
Smaller in $\sqsubseteq$ means **fewer flows** at every point ($\subseteq$ pointwise, §2), i.e. each
call site is claimed to reach a **smaller** set of functions — a **sharper** call graph. So among all
acceptable analyses the least one is the **tightest**. Crucially it is still **sound**: semantic
correctness (file [14](14-0cfa-semantic-correctness.md)) shows *every* acceptable solution
over-approximates the real runtime flows, and acceptability is preserved under evaluation. The least
acceptable solution is thus the **smallest sound over-approximation the 0-CFA specification admits** —
it still lies *above* the (uncomputable) exact flow, but no acceptable analysis lies strictly below
it. "Least in the lattice" and "most precise sound answer" are the same point, viewed from two sides.

### 3.5 Closure-operator view & the bridge to computation
Every Moore family $Y$ induces a **closure operator** $\gamma:L\to L$,
$\gamma(\hat C,\hat\rho)=\sqcap\{(\hat C',\hat\rho')\in Y\mid(\hat C,\hat\rho)\sqsubseteq(\hat C',\hat\rho')\}$
— the **least acceptable solution above a given guess**. Its fixed points are exactly $Y$. This is the
same closure-operator/Galois-connection machinery that underlies abstract interpretation, and it says
an arbitrary guess can always be *improved to* (not just checked against) the nearest acceptable
solution. Because $\mathit{Term}$ restricted to a program's finitely many subterms is finite, $L$
satisfies the ascending chain condition, so this least solution is not merely an existence statement:
it is **computable by fixed-point iteration** — which, via the syntax-directed $\models_s$ of §5, is
what the constraint solver of [16](16-0cfa-constraint-based-solving.md) actually does.

## 4. Why coinduction (not induction)
Acceptability must be read as a **greatest fixpoint (coinductive)**, not a least one.
- With **higher-order recursion**, a value's flow can depend **circularly** on itself (a function
  reaching a call site whose analysis feeds back into that function). The **gfp** reading tolerates
  such self-supporting flows; the **lfp/inductive** reading is **too strict** and collapses them to
  $\varnothing$.
- Concretely: had we defined acceptability inductively as $\models'$, there is a program $e^\ast$
  whose $\models'$-acceptable solutions are **not** a Moore family (the least fixpoint yields a
  "bad" empty set). So **inductive acceptability breaks the least-solution guarantee** — coinduction
  is essential. (This is the same reason the closure/agreement relation in
  [14](14-0cfa-semantic-correctness.md) is coinductive.)

## 5. Toward computation — the syntax-directed specification $\models_s$
The plain $\models$ re-analyses a function body **each time it might be applied**. The
**syntax-directed 0-CFA** $\models_s$ analyses each body **exactly once, at its definition** —
far more computational, and (semantic correctness already handled in
[14](14-0cfa-semantic-correctness.md)) it needs no intermediate expressions.

- New clause: $[\textsf{fn}]\ (\hat C,\hat\rho)\models_s(\mathsf{fn}\ x\Rightarrow e_0)^l \iff \{\mathsf{fn}\ x\Rightarrow e_0\}\subseteq\hat C(l)\ \wedge\ (\hat C,\hat\rho)\models_s e_0$ (body analysed at definition, even if never called).
- **Preservation of solutions:** $(\hat C,\hat\rho)\models_s e^\ast\Rightarrow(\hat C,\hat\rho)\models e^\ast$ (on program terms) — $\models_s$ is a **safe approximation** of $\models$; restricting the range of $\hat C,\hat\rho$ to fragments of $e^\ast$, the two have the **same least solution**. This least $\models_s$ solution is what the constraint system of [16](16-0cfa-constraint-based-solving.md) computes.
- **Definition-Application Decoupling:** $\models_s$ decouples the body analysis of a function from its application site. This is especially important for higher-order recursive functions.
- **More Constrained Analysis**: since $\models_s$ requires to analyze the body of a function even in the case it will never be applied, it demands stricter constraints than $\models$ for dead code. However, if we restrict the analysis to only reachable fragments of the code then both analysis yields the same solution. This is also why the solution preservation and the constrains is defined on $ie$ expressions (so on program fragments).

## 6. Pros / cons / use cases
- **Pros:** guarantees a canonical **best** analysis result; the Moore-family/lattice structure is
  what makes CFA well-defined and computable; $\models_s$ makes it algorithmic.
- **Cons:** the least solution is only *relatively* precise (still 0-CFA / context-insensitive);
  the coinductive subtlety is easy to get wrong.
- **Use cases:** justifies "take *the* CFA of a program"; foundation for the solver
  ([16](16-0cfa-constraint-based-solving.md)) and all refinements.

---

## 📋 Cheatsheet (complete)

### Order on solutions (pointwise; smaller = more precise)
$$(\hat C_1,\hat\rho_1)\sqsubseteq(\hat C_2,\hat\rho_2)\iff\forall l.\ \hat C_1(l)\subseteq\hat C_2(l)\wedge\forall x.\ \hat\rho_1(x)\subseteq\hat\rho_2(x)\quad(\text{complete lattice}).$$

### Moore family & existence
$$Y\ \text{Moore family}\iff\forall Y'\subseteq Y.\ \textstyle\sqcap Y'\in Y.\qquad \{(\hat C,\hat\rho)\mid(\hat C,\hat\rho)\models ie\}\ \text{is a Moore family}.$$
$$\Rightarrow\ \top\ \text{is acceptable (CFA exists)};\quad \textstyle\sqcap\{\text{acceptable}\}\ \text{is the least (best) CFA}.$$

### Coinduction
Acceptability = **greatest fixpoint**. Inductive $\models'$ ⟹ $\exists e^\ast$ whose acceptable set is **not** a Moore family (lfp gives $\varnothing$). Circular higher-order flows need gfp.

### Syntax-directed $\models_s$
Analyse each body **once at definition**: $[\textsf{fn}]\ \{\mathsf{fn}\ x\Rightarrow e_0\}\subseteq\hat C(l)\wedge\models_s e_0$. Preservation: $\models_s\ \Rightarrow\ \models$ (same least solution on program terms) → solved in [16](16-0cfa-constraint-based-solving.md).
