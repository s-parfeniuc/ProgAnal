---
title: Abstract Analysis — Fixpoints, Widening & Narrowing
abbrev: AI (analysis)
lectures: "12 (analysis as fixpoint), 14 (convergence), 15 (Abstract Analysis)"
paper: "Cousot & Cousot, POPL 1977 (widening/narrowing); A. Miné, Tutorial (reading)"
theme: "running the analysis: abstract fixpoints, soundness by fixpoint transfer, termination by widening"
oneliner: "An analysis computes lfp F♯; soundness is fixpoint transfer α(lfp F) ⊑ lfp F♯, termination is bought with widening ∇ and precision recovered with narrowing △."
render: "Notation is LaTeX math ($…$ / $$…$$). Preview with a KaTeX markdown extension."
---

# Abstract Analysis — Fixpoints, Widening & Narrowing

**Theme:** how to *run* an abstract interpretation. The reachable states are a **fixpoint**;
the analysis computes an abstract fixpoint that **soundly over-approximates** it, using
**widening** to guarantee termination and **narrowing** to recover precision. Final part of
the AI block; uses the domains/operators of [10](10-abstract-domains-operators.md) and the
Galois theory of [09](09-order-theory-galois-connections.md).

## 1. Purpose & core idea
The set of reachable states at each program point is the **least solution of a system of
equations** — a **least fixpoint**. It is not computable in general, so the analysis instead
computes the least fixpoint of the **abstract** transfer functions. Two obligations: it must
be **sound** (cover the concrete fixpoint) and it must **terminate** (converge in finitely
many steps).

## 2. Analysis as a fixpoint
Attach to each program point $i$ a **transfer function** $F_i$; the concrete invariants
$S_i$ are the smallest solution of the equation system. For a loop this is a fixpoint:
$$\text{reachable} = \mathrm{lfp}\ \lambda X.\ S_0\cup\llbracket c\rrbracket X \qquad(\text{by Kleene: } \textstyle\bigcup_{k\ge 0}(\lambda X.\dots)^k(\varnothing)).$$
This **strongest invariant is not computable in general**. The **abstract interpreter**
mirrors the concrete one construct-by-construct on the abstract domain:
$$\llbracket c_1;c_2\rrbracket^\sharp=\llbracket c_2\rrbracket^\sharp\circ\llbracket c_1\rrbracket^\sharp,\quad \llbracket c_1{+}c_2\rrbracket^\sharp=\llbracket c_1\rrbracket^\sharp\sqcup\llbracket c_2\rrbracket^\sharp,\quad \llbracket c^\star\rrbracket^\sharp=\lambda S.\ \mathrm{lfp}\ \lambda X.\ S\sqcup\llbracket c\rrbracket^\sharp X.$$
The analysis result at a loop is $\mathrm{lfp}\,F^\sharp$, computed by **Kleene iteration**
$\bot\sqsubseteq F^\sharp(\bot)\sqsubseteq F^\sharp{}^2(\bot)\sqsubseteq\dots$

## 3. Soundness: the fixpoint transfer theorem
> [!important] Fixpoint transfer (why the analysis is sound)
> If $F$ is monotone and $F^\sharp$ is a **sound** abstraction of $F$ (i.e. $\alpha\circ F\sqsubseteq F^\sharp\circ\alpha$, see [10](10-abstract-domains-operators.md)), then
> $$\alpha\big(\mathrm{lfp}\,F\big)\ \sqsubseteq\ \mathrm{lfp}\,F^\sharp \qquad\Big(\text{equivalently } \mathrm{lfp}\,F\ \le\ \gamma(\mathrm{lfp}\,F^\sharp)\Big).$$
> The **abstract fixpoint over-approximates the concrete one** — soundness lifts from single
> operators (via each $F^\sharp$) to the whole least fixpoint. This is the theorem that makes
> the analysis trustworthy.

## 4. The termination problem — widening $\nabla$
Kleene iteration terminates iff the abstract domain satisfies the **Ascending Chain
Condition** (ACC). Many useful domains are **not** ACC — e.g. **Intervals**: iterating a
loop that grows a counter yields $[0,0]\sqsubseteq[0,1]\sqsubseteq[0,2]\sqsubseteq\dots$
forever. Cousot & Cousot's fix is a **widening operator** $\nabla$ that **extrapolates** to a
post-fixpoint in finitely many steps.

> [!note] Widening $\nabla:A\times A\to A$ — definition
> (i) **Covers** its arguments: $a\sqsubseteq a\nabla b$ and $b\sqsubseteq a\nabla b$.
> (ii) **Enforces termination:** for *any* increasing sequence $x_0\sqsubseteq x_1\sqsubseteq\dots$,
> the *widened* sequence $y_0=x_0,\ y_{i+1}=y_i\nabla x_{i+1}$ **stabilises** after finitely many steps.
>
> The loop is then computed as $\llbracket c^\star\rrbracket^\sharp=\lambda S.\ \mathrm{lfp}\ \lambda X.\ S\,\nabla\,\llbracket c\rrbracket^\sharp X$ — the iterates jump to a **stable over-approximation** (a post-fixpoint) instead of climbing forever. Widening **loses precision** to buy termination.

**Interval widening** (the canonical instance): unstable bounds are pushed to infinity,
$$[a,b]\ \nabla\ [a',b']\ =\ [\,(a'<a)\,?\,-\infty:a,\ \ (b'>b)\,?\,+\infty:b\,].$$

## 5. Recovering precision — narrowing $\triangle$
Widening overshoots (often to $[-\infty,+\infty]$ on one side). A **narrowing operator**
$\triangle$ then runs a **decreasing** iteration from the post-fixpoint, tightening the
result **without going below the concrete fixpoint** and still terminating.

> [!note] Narrowing $\triangle:A\times A\to A$ — definition
> (i) **Stays in between:** if $b\sqsubseteq a$ then $b\sqsubseteq a\triangle b\sqsubseteq a$.
> (ii) **Enforces termination** of decreasing iterations.

**Interval narrowing:** refine only the infinite bounds introduced by widening,
$$[a,b]\ \triangle\ [a',b']\ =\ [\,(a=-\infty)\,?\,a':a,\ \ (b=+\infty)\,?\,b':b\,].$$
Typical loop analysis: **iterate with $\nabla$ up to a post-fixpoint, then iterate with
$\triangle$ down** to sharpen it.

## 6. Properties (soundness & termination) + the accelerated interpreter
- **Soundness:** guaranteed by the **fixpoint transfer theorem** (§3), provided each abstract
  operator is sound (§[10](10-abstract-domains-operators.md)); the widened/narrowed result is
  a **sound post-fixpoint**, still $\sqsupseteq\alpha(\mathrm{lfp}\,F)$.
- **Termination:** guaranteed either by an **ACC** domain (plain Kleene) or by **widening**
  (non-ACC domains). Narrowing's decreasing iteration also terminates.
- **Precision/cost knobs:** the domain (see [10](10-abstract-domains-operators.md)), the
  **widening delay** (do $k$ exact steps before widening), and the **narrowing** passes.
- The **accelerated abstract interpreter** is just the abstract interpreter with $\sqcup$
  replaced by $\nabla$ at loops (then a $\triangle$ pass).

## 7. Pros / cons / use cases
- **Pros:** a general, **automatic** recipe to compute sound invariants for **any** sound
  domain, **even without ACC**; precision is tunable (domain, widening delay, narrowing).
- **Cons:** widening is **non-monotone** and its design is delicate (a bad $\nabla$ can wreck
  precision); results are **post-fixpoints**, generally not the best abstraction.
- **Use cases:** the engine inside every abstract-interpretation analyser (Astrée, etc.) —
  loop-invariant inference, bounds/overflow/division-by-zero/array-safety proofs.

---

## 📋 Cheatsheet (complete)

### Analysis = fixpoint
$$\text{concrete reachable} = \mathrm{lfp}\ \lambda X.\ S_0\cup\llbracket c\rrbracket X\ \ (\text{strongest invariant, uncomputable});\qquad \text{analysis} = \mathrm{lfp}\,F^\sharp.$$
Abstract interpreter: $\llbracket c_1;c_2\rrbracket^\sharp=\llbracket c_2\rrbracket^\sharp\circ\llbracket c_1\rrbracket^\sharp$, $\ \llbracket c_1{+}c_2\rrbracket^\sharp=\llbracket c_1\rrbracket^\sharp\sqcup\llbracket c_2\rrbracket^\sharp$, $\ \llbracket c^\star\rrbracket^\sharp=\lambda S.\ \mathrm{lfp}\ \lambda X.\ S\sqcup\llbracket c\rrbracket^\sharp X$.
Kleene: $\mathrm{lfp}\,F^\sharp=\bigsqcup_{k\ge 0}(F^\sharp)^k(\bot)$ (terminates iff ACC).

### Soundness — fixpoint transfer
$$F\text{ monotone},\ \alpha\circ F\sqsubseteq F^\sharp\circ\alpha\ \Longrightarrow\ \alpha(\mathrm{lfp}\,F)\sqsubseteq\mathrm{lfp}\,F^\sharp\ \Longleftrightarrow\ \mathrm{lfp}\,F\le\gamma(\mathrm{lfp}\,F^\sharp).$$

### Widening $\nabla$ (termination for non-ACC domains)
$$a\sqsubseteq a\nabla b,\quad b\sqsubseteq a\nabla b;\qquad y_0=x_0,\ y_{i+1}=y_i\nabla x_{i+1}\ \text{stabilises for every increasing }(x_i).$$
$$\llbracket c^\star\rrbracket^\sharp=\lambda S.\ \mathrm{lfp}\ \lambda X.\ S\,\nabla\,\llbracket c\rrbracket^\sharp X;\qquad [a,b]\nabla[a',b']=[\,a'<a?\,{-\infty}:a,\ b'>b?\,{+\infty}:b\,].$$

### Narrowing $\triangle$ (recover precision)
$$b\sqsubseteq a\ \Rightarrow\ b\sqsubseteq a\triangle b\sqsubseteq a;\quad\text{decreasing iteration terminates};\qquad [a,b]\triangle[a',b']=[\,a{=}{-\infty}?\,a':a,\ b{=}{+\infty}?\,b':b\,].$$
Recipe: iterate up with $\nabla$ to a post-fixpoint, then down with $\triangle$.

### Termination summary
$$\text{ACC domain}\Rightarrow\text{plain Kleene terminates};\qquad \text{non-ACC (e.g. Intervals, Polyhedra)}\Rightarrow\text{use }\nabla\ (+\ \triangle).$$
