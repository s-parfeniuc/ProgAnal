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
$$\underbrace{lhs\subseteq rhs}_{\text{unconditional}}\qquad\qquad \underbrace{\{t\}\subseteq rhs'\ \Rightarrow\ lhs\subseteq rhs}_{\text{conditional: "if }t\text{ may flow to }rhs',\text{ then }lhs\text{ flows to }rhs"}$$
with $lhs::=C(l)\mid r(x)\mid\{t\}$ ($t$ a function abstraction) and $rhs::=C(l)\mid r(x)$. The
generator $\mathcal C^\ast\llbracket e^\ast\rrbracket$ collects all constraints by recursion on syntax.

> [!important] The constraint clauses
> $$\mathcal C^\ast\llbracket c^l\rrbracket=\varnothing\qquad \mathcal C^\ast\llbracket x^l\rrbracket=\{\,r(x)\subseteq C(l)\,\}$$
> $$\mathcal C^\ast\llbracket(\mathsf{fn}\ x\Rightarrow e_0)^l\rrbracket=\{\,\{\mathsf{fn}\ x\Rightarrow e_0\}\subseteq C(l)\,\}\cup\mathcal C^\ast\llbracket e_0\rrbracket$$
> $$\mathcal C^\ast\llbracket(\mathsf{fun}\ f\ x\Rightarrow e_0)^l\rrbracket=\{\,\{\mathsf{fun}\ f\ x\Rightarrow e_0\}\subseteq C(l),\ \ \{\mathsf{fun}\ f\ x\Rightarrow e_0\}\subseteq r(f)\,\}\cup\mathcal C^\ast\llbracket e_0\rrbracket$$
> $$\mathcal C^\ast\llbracket(t_1^{l_1}t_2^{l_2})^l\rrbracket=\mathcal C^\ast\llbracket t_1^{l_1}\rrbracket\cup\mathcal C^\ast\llbracket t_2^{l_2}\rrbracket\ \cup\!\!\!\bigcup_{t=(\mathsf{fn}\ x\Rightarrow t_0^{l_0})\in\mathit{Term}^\ast}\!\!\!\Big\{\ \{t\}\subseteq C(l_1)\Rightarrow C(l_2)\subseteq r(x),\ \ \{t\}\subseteq C(l_1)\Rightarrow C(l_0)\subseteq C(l)\ \Big\}$$
> $$\mathcal C^\ast\llbracket(\mathsf{if}\ t_0^{l_0}\ t_1^{l_1}\ t_2^{l_2})^l\rrbracket=\mathcal C^\ast\llbracket t_0^{l_0}\rrbracket\cup\mathcal C^\ast\llbracket t_1^{l_1}\rrbracket\cup\mathcal C^\ast\llbracket t_2^{l_2}\rrbracket\ \cup\ \{\,C(l_1)\subseteq C(l),\ \ C(l_2)\subseteq C(l)\,\}$$
> $$\mathcal C^\ast\llbracket(\mathsf{let}\ x{=}t_1^{l_1}\ \mathsf{in}\ t_2^{l_2})^l\rrbracket=\mathcal C^\ast\llbracket t_1^{l_1}\rrbracket\cup\mathcal C^\ast\llbracket t_2^{l_2}\rrbracket\ \cup\ \{\,\underbrace{C(l_1)\subseteq r(x)}_{\text{bind}},\ \ \underbrace{C(l_2)\subseteq C(l)}_{\text{result}}\,\}$$
> $$\mathcal C^\ast\llbracket(t_1^{l_1}\,\mathsf{op}\,t_2^{l_2})^l\rrbracket=\mathcal C^\ast\llbracket t_1^{l_1}\rrbracket\cup\mathcal C^\ast\llbracket t_2^{l_2}\rrbracket\quad(\text{no constraint on }C(l):\ \mathsf{op}\text{ yields a base value, like }c^l)$$
> ($\mathit{Term}^\ast$ = the function abstractions — both $\mathsf{fn}$ and $\mathsf{fun}$ — occurring in $e^\ast$.)
> Only **application** produces conditional constraints; every other clause is a fixed, unconditional
> inclusion, read straight off the corresponding $\models$ clause of the specification.

Reading them: **`fun`** is `fn` plus one extra pipe — the closure also flows into the *recursion
variable* $r(f)$, so a call to $f$ inside the body finds the function itself. **`if`** lays a pipe
from *each* branch to the result point (0-CFA never inspects the guard, so both branches are taken
to be possible), while the guard itself only has to be analysed. **`let`** is two pipes: bind
$C(l_1)\subseteq r(x)$, then return $C(l_2)\subseteq C(l)$. **`op`** is a dead end like a constant:
analyse the operands, demand nothing of $C(l)$, since an arithmetic/comparison result is never a
function abstraction.

## 3. Solving — the worklist algorithm
A solution assigns a **value set** (of function abstractions) to each variable $C(l)/r(x)$. Solve
by least-fixpoint propagation:
1. Build a **graph**: one node $q$ per constraint variable, holding a current value set $D[q]$ and
   a **watch-list** $E[q]$ of constraints to replay when $D[q]$ grows. An unconditional
   $lhs\subseteq rhs$ is an edge along which values flow; each conditional constraint is attached to
   the node(s) it watches.
2. Initialise: $D[q]:=\varnothing$, then apply the base constraints $\{t\}\subseteq C(l)$ (seed
   $D[C(l)]$ with $t$ and enqueue $C(l)$).
3. **Worklist propagation:** repeatedly take a node whose set grew, and replay every constraint on
   its watch-list — pushing values along outgoing edges (monotonically enlarging targets), and
   **whenever a watched function $t$ appears in $C(l_1)$, activating** that conditional constraint's
   edge (arg → param, body → call site).
4. Stop at the least fixpoint (no set changes) — that assignment is the least CFA.

### 3.1 The data structures and the loop (NNH, Table 3.7)
Concretely the solver keeps, per node $q$: a set $D[q]$ (current value set) and a list $E[q]$ (the
constraints to re-examine when $D[q]$ changes). Growth is funnelled through one helper, which is the
**only** place the worklist $W$ grows:
$$\textbf{add}(q,d):\quad \text{if } d\not\subseteq D[q]\ \text{then } D[q]:=D[q]\cup d;\ W:=q::W.$$
Building the graph registers each constraint on the watch-list(s) of the node(s) that can *trigger*
it — and this registration is where the subtlety lives:
$$\begin{aligned}
\{t\}\subseteq p&:&&\textbf{add}(p,\{t\})\quad(\text{seed, no watch})\\
p_1\subseteq p_2&:&&E[p_1]\mathrel{+}=cc\\
\{t\}\subseteq p\Rightarrow p_1\subseteq p_2&:&&E[p_1]\mathrel{+}=cc\ \textbf{ and }\ E[p]\mathrel{+}=cc\quad(\textbf{both}).
\end{aligned}$$
Then iterate: dequeue $q$ from $W$ and, for each $cc\in E[q]$,
$$p_1\subseteq p_2\ \leadsto\ \textbf{add}(p_2,D[p_1]);\qquad
\{t\}\subseteq p\Rightarrow p_1\subseteq p_2\ \leadsto\ \textbf{if } t\in D[p]\ \textbf{then } \textbf{add}(p_2,D[p_1]).$$

### 3.2 The subtle case: activate an edge on the source's *existing* contents
A conditional $\{t\}\subseteq C(l_1)\Rightarrow C(l_3)\subseteq C(l_4)$ has **three** points, and the
guard token $t$ may reach the watched node $C(l_1)$ **after** the source $C(l_3)$ already holds
values. At that instant the edge $C(l_3)\to C(l_4)$ switches on and $C(l_3)$'s **already-present**
contents must flow to $C(l_4)$ — even though nothing *new* just entered $C(l_3)$. A naïve loop that
only re-scans a node when it grows would miss exactly this.

The dual registration in §3.1 is what prevents the miss. Because $cc$ sits on **both** $E[C(l_1)]$
(the guard) **and** $E[C(l_3)]$ (the source), whichever of the two events happens second re-fires it:
- the **source** $C(l_3)$ grows first, guard not yet set → firing finds $t\notin D[C(l_1)]$, does
  nothing; later $t$ arrives at $C(l_1)$ → dequeuing $C(l_1)$ replays $cc$, now $t\in D[C(l_1)]$, so
  $\textbf{add}(C(l_4),D[C(l_3)])$ copies $C(l_3)$'s **current** set across;
- the **guard** $t$ arrives first → the edge is live, and any *future* growth of $C(l_3)$ replays
  $cc$ from $E[C(l_3)]$ and pushes the new values on.

> [!note] The invariant to remember
> **An edge that becomes active must fire on the source's values already present, not only on values
> that arrive afterwards.** Registering each conditional on *both* the guard node and the source node
> guarantees it, whichever event is second — and dequeuing the **guard** node propagates
> $D[\text{source}]$ **directly** to the target (the source node is *not* re-enqueued; enqueuing it
> would reach the same fixpoint but redundantly re-scan its whole watch-list). Because every
> $D[q]\subseteq\mathit{Term}^\ast$ is finite and $\textbf{add}$ only ever enlarges sets, the loop is
> monotone and terminates at the least fixpoint.

## 4. Properties — preservation & complexity (with *why*)
- **Preservation of solutions.** For $(\hat C,\hat\rho)\sqsubseteq(\hat C_\top,\hat\rho_\top)$:
  $(\hat C,\hat\rho)\models_c\mathcal C^\ast\llbracket e^\ast\rrbracket\iff(\hat C,\hat\rho)\models_s e^\ast$
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
Satisfaction $\models_c$: $(\hat C,\hat\rho)\models_c(lhs\subseteq rhs)\iff\llbracket lhs\rrbracket\subseteq\llbracket rhs\rrbracket$; a conditional holds iff $t\in\llbracket rhs'\rrbracket\Rightarrow$ its body holds.

### Generation $\mathcal C^\ast\llbracket\cdot\rrbracket$
$$c^l\mapsto\varnothing,\quad x^l\mapsto\{r(x)\subseteq C(l)\},\quad (\mathsf{fn}\ x\Rightarrow e_0)^l\mapsto\{\{\mathsf{fn}\dots\}\subseteq C(l)\}\cup\mathcal C^\ast\llbracket e_0\rrbracket$$
$$(t_1^{l_1}t_2^{l_2})^l\mapsto\mathcal C^\ast\llbracket t_1\rrbracket\cup\mathcal C^\ast\llbracket t_2\rrbracket\cup\{\{t\}\subseteq C(l_1)\Rightarrow C(l_2)\subseteq r(x),\ \{t\}\subseteq C(l_1)\Rightarrow C(l_0)\subseteq C(l)\mid t=(\mathsf{fn}\ x\Rightarrow t_0^{l_0})\in\mathit{Term}^\ast\}.$$

### Solving
Per node $q$: value set $D[q]$ + watch-list $E[q]$; growth only via $\textbf{add}(q,d)$ (enlarge $D[q]$, enqueue $q$). Unconditional = static edge; conditional $\{t\}\subseteq p\Rightarrow p_1\subseteq p_2$ registered on **both** $E[p]$ (guard) **and** $E[p_1]$ (source), fires $\textbf{add}(p_2,D[p_1])$ when $t\in D[p]$. Dual registration ⇒ a newly-activated edge propagates the source's **already-present** contents, not just future arrivals. Iterate to least fixpoint = least CFA.

### Theorems
- **[Preservation]** least solution of $\mathcal C^\ast\llbracket e^\ast\rrbracket$ = least CFA ($\models_s$/$\models$).
- **[Complexity]** $O(n)$ constraints, $O(n^2)$ conditional; **$O(n^3)$** worst-case solving — polynomial despite higher-order functions.
