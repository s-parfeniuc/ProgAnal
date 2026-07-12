---
title: 0-CFA — Constraint-Based Formulation & Solving
abbrev: CFA (constraints)
lectures: "20 (CFA — constraints & solving)"
paper: "Nielson, Nielson & Hankin, Principles of Program Analysis, Ch. 3"
theme: "turn the CFA specification into a solvable constraint system and compute its least solution"
oneliner: "Generate a finite set of (conditional) inclusion constraints from the syntax; solve them by worklist propagation for the least CFA — cubic in program size."
render: "Notation is LaTeX math ($…$ / $$…$$). Preview with a KaTeX markdown extension."
---

# 0-CFA — Constraint-Based Formulation & Solving

**Theme:** the *algorithmic* side of CFA. The least solution shown to exist in
[15](15-0cfa-existence-least-solutions.md) is computed by **generating inclusion constraints**
from the program and **propagating** to their least fixpoint. This is the form implemented in
real tools.

## 1. Purpose & core idea
The syntax-directed specification $\models_s$ is close to an algorithm but still a logical
relation. The constraint-based approach makes it fully mechanical: **each syntactic construct
emits a fixed set of inclusion constraints** over unknowns, and the **least solution of the
constraint system is exactly the least CFA**. Higher-order calls are handled by **conditional
constraints** that fire when a function is discovered to flow to a call site.

## 2. From rules to constraints
Replace the unknowns $\hat C(l),\hat\rho(x)$ by **constraint variables** $C(l), r(x)$. Two
constraint shapes:
$$\underbrace{\text{lhs}\subseteq \text{rhs}}_{\text{unconditional}}\qquad\qquad \underbrace{\{t\}\subseteq \text{rhs}'\ \Rightarrow\ \text{lhs}\subseteq \text{rhs}}_{\text{conditional: "if }t\text{ may flow to }\text{rhs}',\text{ then }\text{lhs}\text{ flows to }\text{rhs}"}$$
with $\text{lhs}::=C(l)\mid r(x)\mid\{t\}$ ($t$ a function abstraction) and $\text{rhs}::=C(l)\mid r(x)$. The
generator $\mathcal C^\ast[\![  e^\ast ]\!]$ collects all constraints by recursion on syntax.

> [!important] The constraint clauses
> $$\mathcal C^\ast[\![  c^l ]\!]=\varnothing\qquad \mathcal C^\ast[\![  x^l ]\!]=\{\,r(x)\subseteq C(l)\,\}$$
> $$\mathcal C^\ast[\![ (\mathsf{fn}\ x\Rightarrow e_0)^l ]\!]=\{\,\{\mathsf{fn}\ x\Rightarrow e_0\}\subseteq C(l)\,\}\cup\mathcal C^\ast[\![  e_0 ]\!]$$
> $$\mathcal C^\ast[\![ (t_1^{l_1}t_2^{l_2})^l ]\!]=\mathcal C^\ast[\![  t_1^{l_1} ]\!]\cup\mathcal C^\ast[\![  t_2^{l_2} ]\!]\ \cup\!\!\!\bigcup_{t=(\mathsf{fn}\ x\Rightarrow t_0^{l_0})\in\mathit{Term}^\ast}\!\!\!\Big\{\ \{t\}\subseteq C(l_1)\Rightarrow C(l_2)\subseteq r(x),\ \ \{t\}\subseteq C(l_1)\Rightarrow C(l_0)\subseteq C(l)\ \Big\}$$
> ($\mathit{Term}^\ast$ = the function abstractions occurring in $e^\ast$; `let`, `if`, `op`, `fun` are analogous). Only **application** produces conditional constraints.

## 3. Solving — the worklist algorithm
A solution assigns a **value set** (of function abstractions) to each variable $C(l)/r(x)$. Solve
by least-fixpoint propagation:
1. Build a **graph**: one node per constraint variable; an unconditional $lhs\subseteq rhs$ is an
   edge along which values flow; each conditional constraint is attached to the node $C(l_1)$ it
   watches.
2. Initialise each node's value set from the base constraints ($\{t\}\subseteq C(l)$).
3. **Worklist propagation:** repeatedly take a node whose set grew, push its values along outgoing
   edges (monotonically enlarging targets), and **whenever a watched function $t$ appears in
   $C(l_1)$, activate** that conditional constraint's edge (arg → param, body → call site).
4. Stop at the least fixpoint (no set changes) — that assignment is the least CFA.

## 4. Properties — preservation & complexity (with *why*)
- **Preservation of solutions.** For $(\hat C,\hat\rho)\sqsubseteq(\hat C_\top,\hat\rho_\top)$:
  $(\hat C,\hat\rho)\models_c\mathcal C^\ast[\![  e^\ast ]\!]\iff(\hat C,\hat\rho)\models_s e^\ast$
  (on program terms). **Hence the least constraint solution *is* the least CFA** of
  [15](15-0cfa-existence-least-solutions.md). *Why:* by structural induction; the application case
  uses $\hat C(l_1)\subseteq\mathit{Term}^\ast$ so only real program functions are ever propagated.
- **Complexity.** For $|e^\ast|=n$: every construct except application emits $O(1)$ constraints;
  each application emits $O(1)$ plain and $O(n)$ conditional constraints — so $O(n)$ constraints
  and $O(n^2)$ conditional ones. Worklist solving is then **cubic, $O(n^3)$**, in the worst case.
  **The analysis stays polynomial despite higher-order functions** — the headline efficiency fact.

## 5. Peculiarities & connections
- **Conditional constraints are the essence:** they let the call graph be discovered *during*
  solving (dynamic edges), which is how higher-order dispatch is resolved.
- Equivalent to the Flow-Logic $\models$/$\models_s$ ([13](13-cfa-motivation-0cfa-specification.md),
  [15](15-0cfa-existence-least-solutions.md)) — same least solution, packaged for solving.
- The cubic bottleneck ("$O(n^3)$") is the classic 0-CFA complexity; sub-cubic variants and the
  precision/cost trade-off motivate the refinements of [17](17-beyond-0cfa-abstract-values-context.md).

## 6. Pros / cons / use cases
- **Pros:** fully mechanical; a single least-fixpoint computation; standard graph/worklist solver;
  polynomial even for higher-order code.
- **Cons:** cubic worst case; still 0-CFA (context-insensitive); conditional-constraint bookkeeping.
- **Use cases:** the actually-implemented form of CFA in compilers/analysers; template for
  set-constraint analyses generally.

---

## 📋 Cheatsheet (complete)

### Constraint language
$$lhs\subseteq rhs\qquad\text{and}\qquad \{t\}\subseteq rhs'\Rightarrow lhs\subseteq rhs;\qquad lhs::=C(l)\mid r(x)\mid\{t\},\quad rhs::=C(l)\mid r(x).$$
Satisfaction $\models_c$: $(\hat C,\hat\rho)\models_c(lhs\subseteq rhs)\iff[\![  lhs ]\!]\subseteq[\![  rhs ]\!]$; a conditional holds iff $t\in[\![  rhs' ]\!]\Rightarrow$ its body holds.

### Generation $\mathcal C^\ast[\![ \cdot ]\!]$
$$c^l\mapsto\varnothing,\quad x^l\mapsto\{r(x)\subseteq C(l)\},\quad (\mathsf{fn}\ x\Rightarrow e_0)^l\mapsto\{\{\mathsf{fn}\dots\}\subseteq C(l)\}\cup\mathcal C^\ast[\![  e_0 ]\!]$$
$$(t_1^{l_1}t_2^{l_2})^l\mapsto\mathcal C^\ast[\![  t_1 ]\!]\cup\mathcal C^\ast[\![  t_2 ]\!]\cup\{\{t\}\subseteq C(l_1)\Rightarrow C(l_2)\subseteq r(x),\ \{t\}\subseteq C(l_1)\Rightarrow C(l_0)\subseteq C(l)\mid t=(\mathsf{fn}\ x\Rightarrow t_0^{l_0})\in\mathit{Term}^\ast\}.$$

### Solving
Graph of value sets + worklist; unconditional = static edge; conditional = edge activated when watched function reaches $C(l_1)$; iterate to least fixpoint = least CFA.

### Theorems
- **[Preservation]** least solution of $\mathcal C^\ast[\![  e^\ast ]\!]$ = least CFA ($\models_s$/$\models$).
- **[Complexity]** $O(n)$ constraints, $O(n^2)$ conditional; **$O(n^3)$** worst-case solving — polynomial despite higher-order functions.
