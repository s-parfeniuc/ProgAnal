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
> A **Moore family** is a subset $Y$ of a complete lattice closed under **glbs**:
> $\sqcap Y'\in Y$ for every $Y'\subseteq Y$. It always contains a **least** element
> $\sqcap Y$ and a **greatest** $\sqcap\varnothing=\top$, and is **never empty**.
>
> **Theorem.** For every $ie$, the set $\{(\hat C,\hat\rho)\mid(\hat C,\hat\rho)\models ie\}$ of
> acceptable analyses **is a Moore family** (proof by coinduction on $ie$: if all
> $(\hat C_i,\hat\rho_i)\models ie$ then $\sqcap_i(\hat C_i,\hat\rho_i)\models ie$).
>
> **Corollaries:** (i) taking $Y'=\varnothing$ gives $\top\models ie$ — **every expression admits
> a CFA**; (ii) taking $Y'=$ all acceptable solutions gives $\sqcap Y'\models ie$ — the
> **least (most precise) CFA exists**, and it is below every other acceptable solution.

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
$$Y\ \text{Moore family}\iff\forall Y'\subseteq Y.\ \sqcap Y'\in Y.\qquad \{(\hat C,\hat\rho)\mid(\hat C,\hat\rho)\models ie\}\ \text{is a Moore family}.$$
$$\Rightarrow\ \top\ \text{is acceptable (CFA exists)};\quad \sqcap\{\text{acceptable}\}\ \text{is the least (best) CFA}.$$

### Coinduction
Acceptability = **greatest fixpoint**. Inductive $\models'$ ⟹ $\exists e^\ast$ whose acceptable set is **not** a Moore family (lfp gives $\varnothing$). Circular higher-order flows need gfp.

### Syntax-directed $\models_s$
Analyse each body **once at definition**: $[\textsf{fn}]\ \{\mathsf{fn}\ x\Rightarrow e_0\}\subseteq\hat C(l)\wedge\models_s e_0$. Preservation: $\models_s\ \Rightarrow\ \models$ (same least solution on program terms) → solved in [16](16-0cfa-constraint-based-solving.md).
