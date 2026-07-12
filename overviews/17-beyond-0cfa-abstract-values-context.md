---
title: Beyond 0-CFA — Abstract Values & Context Sensitivity
abbrev: CFA (refinements)
lectures: "21 (abstract values, k-CFA), 22 Part 1 (CPA)"
paper: "Nielson, Nielson & Hankin, Principles of Program Analysis, Ch. 3; Shivers (k-CFA); Agesen (CPA)"
theme: "improving 0-CFA precision: richer abstract values (CFA+DFA) and calling-context sensitivity (k-CFA, CPA)"
oneliner: "Add a data lattice to track values (CFA+DFA / monotone frameworks) and split analysis by calling context (k-CFA, Cartesian Product Algorithm) to sharpen 0-CFA."
render: "Notation is LaTeX math ($…$ / $$…$$). Preview with a KaTeX markdown extension."
---

# Beyond 0-CFA — Abstract Values & Context Sensitivity

**Theme:** 0-CFA ([13](13-cfa-motivation-0cfa-specification.md)–[16](16-0cfa-constraint-based-solving.md))
is sound but blunt: it tracks only functions, and merges all calls of a function into one summary.
This file adds the two standard precision axes — **richer abstract values** (bring data-flow in)
and **context sensitivity** (distinguish calling contexts).

## 1. Purpose & core idea
Two sources of 0-CFA imprecision, two fixes:
1. **No data.** Pure CFA carries sets of function terms only. Replace the data component by a
   **complete lattice** and you get a combined **control- + data-flow** analysis (e.g. constant
   propagation) — the CFA determines the flow, the lattice tracks the values along it.
2. **Context-insensitivity.** 0-CFA uses one $\hat\rho(x)$ per variable, mixing every call. Add a
   **calling context** and analyse each context separately — **k-CFA** and the **Cartesian Product
   Algorithm**. Precision rises; so does cost.

## 2. Abstract values as complete lattices (CFA + DFA)
Split an abstract value into **term** info (functions, for control) and **data** info (values):
$$\hat v\in\widehat{\mathit{Val}}_d=\wp(\mathit{Term}\cup\mathit{Data})\equiv\wp(\mathit{Term})\times\wp(\mathit{Data}),\qquad \text{then replace }\wp(\mathit{Data})\text{ by a complete lattice }L.$$
This mirrors (forward) **Monotone Frameworks** — the data-flow-analysis machinery. A **monotone
structure** is a complete lattice $L$ plus a set $F$ of monotone functions $L\times L\to L$; an
*instance* fixes $\iota_c\in L$ for each constant and $f_{\mathsf{op}}\in F$ for each operator. No
flow component is needed — CFA supplies the flow.

> [!example] Constant propagation as a CFA+DFA instance (lect. 21)
> The lecture first gives the **generic powerset instance** — $L=\wp(\mathit{Data})$, $\iota_c=\{d_c\}$, and
> $f_{\mathsf{op}}(l_1,l_2)=\bigcup\{d_{\mathsf{op}}(d_1,d_2)\mid d_1\in l_1,\,d_2\in l_2\}$ (apply the op to *all pairs
> of possible values*; here the members $d_i\in l_i$ make sense because elements **are** sets). Constant
> propagation is then a different, **flat-lattice** instance:
> $$L=\mathbb Z^\top_\bot\times\wp(\mathbb B)\quad(\text{flat integers, }\top=\text{``non-constant''; paired with a set of booleans}),$$
> $\iota_7=(7,\varnothing)$, $\iota_{\mathit{true}}=(\bot,\{\mathit{true}\})$. Its $f_+$ is defined **by cases on the pair**,
> *not* by a comprehension (elements are lattice points, not sets):
> $$f_+(l_1,l_2)=\begin{cases}(z_1+z_2,\varnothing)&l_1=(z_1,\_),\,l_2=(z_2,\_),\ z_1,z_2\in\mathbb Z\\ (\bot,\varnothing)&z_1=\bot\ \text{or}\ z_2=\bot\\ (\top,\varnothing)&\text{otherwise}\end{cases}$$
> i.e. propagate the constant when both operands are known, else fall to $\top$ ("non-constant"). Now $\hat C$/$\hat D$
> track *both* which functions and which constant values reach each point; $[\textsf{con}]/[\textsf{op}]$ use $L$,
> $[\textsf{if}]$ joins branches. Correctness is proved by **staging** the specification (CFA layer + data layer).

## 3. Context sensitivity — k-CFA
Add a **context** $\delta\in\Delta$ recording *how* a point was reached (classically the last $k$
call-site labels — a **call string**). The domains become context-indexed:
$$\hat\rho\in\widehat{\mathit{Cenv}}:(\mathit{Var}\times\Delta)\to\widehat{\mathit{Val}},\qquad \hat C\in\widehat{\mathit{Cache}}:(\mathit{Lab}\times\Delta)\to\widehat{\mathit{Val}}.$$
The acceptability relation gains a context parameter (**uniform k-CFA**, $\models_{ce}$): each clause
carries the current context, and application enters a **new context** derived from the call site.

- **0-CFA** = $k=0$ (one context: fully merged).
- **1-CFA** distinguishes calls by their immediate call site — so two applications of the *same*
  function no longer pollute each other (e.g. `(f g) + (f h)` keeps `g` and `h` separate).
- Precision grows with $k$, but so does cost: **k-CFA is exponential in $k$** (k-CFA for $k\ge 1$
  is famously expensive).

## 4. The Cartesian Product Algorithm (CPA)
A different context choice: the context is the **tuple of actual argument values** at a call, not
the call site. For multi-argument FUN ($\mathsf{fn}\ x_1,\dots,x_m\Rightarrow e_b$, closed
abstractions, no recursion):
$$\delta\in\Delta=\mathit{Term}^m,\qquad \hat\rho:(\mathit{Var}\times\Delta)\to\widehat{\mathit{Val}},\quad \hat C:(\mathit{Lab}\times\Delta)\to\widehat{\mathit{Val}}.$$
CPA **partitions the flow of values according to the actual argument types in the dynamic calling
context** — analysing a function separately for each *combination* of argument abstractions
(the "Cartesian product" of the argument value-sets). It is a value-based refinement of 0-CFA,
often more precise than uniform k-CFA for polymorphic code, and is the basis of practical
higher-order/OO analyses (Self, etc.).

## 5. Properties & trade-offs
- **All remain sound** — each refinement is an abstract interpretation with its own correctness
  (staged specification / subject reduction in the extended domain).
- **Precision vs cost** is the whole story: data lattices add DFA precision; contexts add
  call-site/argument precision; both enlarge the state space (context-indexed caches/environments).
  0-CFA is the cheap baseline; k-CFA and CPA buy precision at real cost.
- Same **least-solution / constraint-solving** structure as 0-CFA — just over context-indexed
  variables (Moore family + worklist still apply, cf. [15](15-0cfa-existence-least-solutions.md),
  [16](16-0cfa-constraint-based-solving.md)).

## 6. Pros / cons / use cases
- **Pros:** tunable precision (data + context); reuses the 0-CFA framework; CFA+DFA unifies control-
  and data-flow; CPA/k-CFA resolve polymorphic dispatch precisely.
- **Cons:** cost blows up (k-CFA exponential in $k$; CPA exponential in argument value-sets);
  choosing the right context is an engineering trade-off.
- **Use cases:** optimising compilers for functional/OO languages; precise devirtualisation;
  combined value+flow analyses.

---

## 📋 Cheatsheet (complete)

### CFA + DFA (abstract values as a lattice)
$$\widehat{\mathit{Val}}_d\equiv\wp(\mathit{Term})\times L\ (L\text{ a complete lattice});\quad \textbf{monotone structure }(L,F),\ F\subseteq[L\times L\to L]\text{ monotone};\quad \text{instance: }\iota_c\in L,\ f_{\mathsf{op}}\in F.$$
Powerset instance: $L=\wp(\mathit{Data})$, $f_{\mathsf{op}}(l_1,l_2)=\bigcup\{d_{\mathsf{op}}(d_1,d_2)\mid d_i\in l_i\}$. Constant propagation instance: $L=\mathbb Z^\top_\bot\times\wp(\mathbb B)$ (flat), $\iota_7=(7,\varnothing)$; $f_+((z_1,\_),(z_2,\_))=(z_1{+}z_2,\varnothing)$ if $z_1,z_2\in\mathbb Z$, $(\bot,\varnothing)$ if either is $\bot$, else $(\top,\varnothing)$.

### Context sensitivity (k-CFA)
$$\delta\in\Delta\ (\text{last }k\text{ call sites});\quad \hat\rho:(\mathit{Var}\times\Delta)\to\widehat{\mathit{Val}},\ \hat C:(\mathit{Lab}\times\Delta)\to\widehat{\mathit{Val}};\quad k{=}0:\text{0-CFA},\ k{=}1:\text{split by call site}.$$
Precision $\uparrow$ with $k$; cost **exponential in $k$**.

### Cartesian Product Algorithm (CPA)
$$\delta\in\Delta=\mathit{Term}^m\ (\text{tuple of argument abstractions});\quad \text{analyse each function per argument-tuple context (Cartesian product of arg value-sets)}.$$

### Trade-off
$$\text{0-CFA (cheap, blunt)}\ \xrightarrow[\text{cost}\uparrow]{\text{+data lattice, +context}}\ \text{CFA+DFA / k-CFA / CPA (precise, costly)};\quad\text{all sound.}$$
