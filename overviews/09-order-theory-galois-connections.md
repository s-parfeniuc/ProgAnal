---
title: Order Theory & Galois Connections
abbrev: AI (Galois)
lectures: "13 (Galois v2)"
paper: "A. Miné, Tutorial on Static Inference of Numeric Invariants, §2 (reading); Cousot & Cousot 1979"
theme: "the formal contract between the concrete and abstract worlds"
oneliner: "A Galois connection α ⊣ γ pairs concrete and abstract domains so the abstraction is sound and as precise as possible."
render: "Notation is LaTeX math ($…$ / $$…$$). Preview with a KaTeX markdown extension."
---

# Order Theory & Galois Connections

**Theme:** the order-theoretic machinery that makes abstraction *sound* and *optimal*.
Part II of the AI block — it formalises the `α`/`γ` sketched in
[08 Intro](08-intro-abstract-interpretation.md) and underpins
[10 domains & operators](10-abstract-domains-operators.md) and
[11 analysis & fixpoints](11-abstract-analysis-fixpoints-widening.md).

## 1. Purpose & core idea
Concrete and abstract worlds are both **ordered by precision**. The **Galois connection**
is the exact relationship $\alpha\dashv\gamma$ between them that guarantees: (i) every
abstract answer is a **sound** over-approximation of the concrete one, and (ii) each
concrete element has a **best** (most precise) abstraction. Order theory (posets, lattices,
lubs/glbs) is the language; the Galois connection is the contract.

## 2. Order-theory prerequisites
- **Poset** $(X,\sqsubseteq)$: a set with a reflexive, antisymmetric, transitive order.
  Here $\sqsubseteq$ reads as "more precise / more information than". See [[glossary]].
- **lub / glb**: the least upper bound $\bigsqcup A$ (join $\sqcup$) and greatest lower bound
  $\sqcap A$ (meet $\sqcap$) of a set $A$.
- **Lattice**: every pair has a lub and glb. **Complete lattice** $(X,\sqsubseteq,\sqcup,\sqcap,\bot,\top)$:
  *every* subset (incl. infinite) has a lub and glb; then $\bot=\bigsqcup\varnothing=\sqcap X$
  and $\top=\sqcap\varnothing=\bigsqcup X$. Example: $(\wp(\mathbb Z),\subseteq,\cup,\cap,\varnothing,\mathbb Z)$.

> [!note] When is a lattice *not* complete?
> A lattice only guarantees **finite** lubs/glbs (pairs); completeness fails when some
> **infinite** subset has no lub. Either **unbounded** — $(\mathbb Z,\le)$: the chain
> $0\sqsubset1\sqsubset\cdots$ has no upper bound (no $\top$) — or **bounded with a missing
> limit** — $(\mathbb Q,\le)$: $\{q\mid q^2<2\}$ is bounded by $2$ but its lub $\sqrt2\notin\mathbb Q$.
> **Course case:** intervals with *finite* bounds $\{[a,b]\mid a,b\in\mathbb Z\}\cup\{\bot\}$ are a
> lattice but **not** complete — $\{[0,i]\mid i\ge0\}$ has no lub (it would be $[0,+\infty]$, outside
> the domain); allowing $\pm\infty$ bounds completes it (then a complete lattice / CPO, but still
> **not ACC** — the chain never stabilises, hence widening). **Finite lattices are always complete.**

- **CPO**: every ascending chain has a lub (pointed CPO also has $\bot$).
- **Ascending Chain Condition (ACC)**: no infinite strictly-ascending chains — every
  ascending chain eventually stabilises. **ACC domains guarantee the analysis terminates**
  (its increasing fixpoint iteration converges). (Note: complete lattice $\not\Rightarrow$ ACC —
  e.g. intervals are a complete lattice but not ACC.)

> [!note] CPO vs ACC — "the limit exists" vs "you reach it"
> Both concern ascending chains $x_0\sqsubseteq x_1\sqsubseteq\cdots$. Read $\sqsubseteq$ as
> "carries more information"; a chain is then a **process accumulating information one step
> at a time** — a staircase of ever-more-complete answers.
> - **CPO** = *every such staircase has a top landing present in the space*: the lub
>   $\bigsqcup_i x_i$ exists. The ascent may be **infinite**, as long as a limit sits at the
>   top. ⟶ guarantees the **limit exists**.
> - **ACC** = *no staircase is infinitely tall*: every strictly-ascending chain
>   **stabilises** after finitely many steps. ⟶ guarantees you **reach** the top in finite time.
>
> **Relationship: $\text{ACC}\Rightarrow\text{CPO}$, but $\text{CPO}\not\Rightarrow\text{ACC}$** —
> ACC is strictly stronger. If a chain stabilises at $x_{n_0}$, that value *is* its maximum,
> hence trivially its lub, so ACC yields chain-lubs for free (always attained, never "out at
> infinity"). A CPO instead permits an infinite strict chain whose lub exists only as a
> genuine limit.
>
> | poset | CPO? | ACC? |
> |---|---|---|
> | even numbers $\{0,2,4,\dots\}$ with $\le$ | **no** (chain has no upper bound) | **no** |
> | $(\mathbb N\cup\{\top\},\le)$ | **yes** (lub $=\top$) | **no** (climbs forever) |
> | Intervals, $\wp(\mathbb Z)$, $[0,1]\subseteq\mathbb R$ | **yes** (complete lattice) | **no** |
> | Signs / any finite-height lattice | **yes** | **yes** |
>
> **Why it matters (→ [11 fixpoints & widening](11-abstract-analysis-fixpoints-widening.md)):**
> for the Kleene chain $\bot\sqsubseteq F^\sharp(\bot)\sqsubseteq (F^\sharp)^2(\bot)\sqsubseteq\cdots$,
> **CPO $\Rightarrow \mathrm{lfp}\,F^\sharp$ exists**, whereas **ACC $\Rightarrow$ the iteration
> terminates** (reaches it in finitely many steps). The concrete domain $\wp(\Sigma)$ is a
> complete lattice (CPO) but **not** ACC — the strongest invariant exists but is not finitely
> computable, *which is a core reason we abstract*. Non-ACC abstract domains (Intervals,
> Octagons, Polyhedra) are CPO-but-not-ACC, so the abstract $\mathrm{lfp}$ exists yet is
> unreachable in finite steps — hence **widening** $\nabla$ is needed to force convergence.
>
> *Height nuance:* **finite height $\Rightarrow$ ACC**, but **ACC $\not\Rightarrow$ finite
> height** — a domain can have strictly-ascending chains of *every finite length* (infinite
> height) yet contain no single *infinite* chain, and so still satisfy ACC.

- **Function properties** (for $f$ between posets): **monotone** ($x\sqsubseteq y\Rightarrow f(x)\sqsubseteq f(y)$),
  **continuous** (preserves lubs of chains), **join-morphism** (preserves all lubs);
  **extensive** ($a\sqsubseteq f(a)$) / **reductive** ($f(a)\sqsubseteq a$).

## 3. Abstraction, concretization & the Galois connection
Two posets: the **concrete** $(C,\le)$ (e.g. $\wp(\mathbb Z)$) and the **abstract**
$(A,\sqsubseteq)$ (e.g. intervals). Two monotone maps:
- **Concretization** $\gamma:A\to C$ — the *meaning* of an abstract element (the set of
  concrete values it stands for).
- **Abstraction** $\alpha:C\to A$ — the **most precise abstract element** describing a
  concrete one.

> [!important] Galois connection (Def.)
> $(\alpha,\gamma)$ is a **Galois connection** iff
> $$\forall c\in C,\ a\in A:\qquad \alpha(c)\sqsubseteq a \iff c\le\gamma(a).$$
> Written $(C,\le)\ \xrightleftharpoons[\alpha]{\gamma}\ (A,\sqsubseteq)$. $\alpha$ and $\gamma$ are **adjoints**
> (course/Miné: $\alpha$ the upper, $\gamma$ the lower adjoint). Either map **determines the
> other** uniquely: $\alpha(c)=\sqcap\{a\mid c\le\gamma(a)\}$, $\gamma(a)=\bigsqcup\{c\mid\alpha(c)\sqsubseteq a\}$.

> [!tip] Reading the biconditional intuitively
> **Both sides say the same thing — "$a$ is a *sound* abstract description of $c$" — but check
> it in different worlds.** Right, $c\le\gamma(a)$: every state of $c$ satisfies $a$ (checked
> **concretely**, $a$ over-approximates $c$). Left, $\alpha(c)\sqsubseteq a$: the *tightest*
> description of $c$ is already $\sqsubseteq a$ (checked **abstractly**). A Galois connection
> promises these two soundness checks **always agree** — so you may verify soundness on either
> side. Equivalently, $\alpha$ = "**round $c$ up** to the tightest expressible description" and
> $\gamma$ = "**unfold** $a$ to its full meaning", and the law says these best-operators are
> *mutually optimal*. Example (intervals): $\underbrace{\alpha(c)}_{\text{smallest box around }c}\sqsubseteq[l,u]\iff c\subseteq\{l,\dots,u\}$;
> analogy (ceiling): $\lceil x\rceil\le n\iff x\le n$. Putting $a=\alpha(c)$ yields
> $c\le\gamma(\alpha(c))$ — **soundness and best precision fall out of the one biconditional**.

The biconditional bundles the **soundness square** of [08](08-intro-abstract-interpretation.md)
into two equivalent inequalities:
$$c\ \le\ \gamma(\alpha(c))\quad(\text{abstract then concretize loses info — sound})\qquad \alpha(\gamma(a))\ \sqsubseteq\ a\quad(\text{concretize then abstract is at least as precise}).$$
$\gamma\circ\alpha$ is **extensive** (over-approximates); $\alpha\circ\gamma$ is **reductive**.

> [!note] What "$\alpha\circ\gamma$ reductive" really shrinks
> It does **not** shrink the concrete *set*: reductive + extensive force the identity
> $\gamma(\alpha(\gamma(a)))=\gamma(a)$ (the **$\gamma\alpha\gamma=\gamma$** law), so the *meaning*
> is untouched. What can strictly shrink is the abstract **element**: $\alpha(\gamma(a))\sqsubset a$
> happens exactly when $a$ is a **redundant** element ($\gamma$ non-injective) and a smaller one
> denotes the same set — then $\alpha$ (which returns the *best* abstraction) maps $a$ **down to
> that canonical representative**. E.g. a spurious $p$ with $\gamma(p)=\gamma(+)$ and $+\sqsubset p$:
> $\alpha(\gamma(p))=\alpha(\text{positives})=+\sqsubset p$. **$\alpha\circ\gamma=\mathrm{id}$ exactly
> in a Galois *insertion*** (no redundant elements); a plain GC only tightens redundant elements to
> their canonical form.

**Best abstraction.** In a Galois connection, $\alpha(c)$ is the **best** (most precise)
sound over-approximation of $c$: $c\le\gamma(a)\iff\alpha(c)\sqsubseteq a$. For $\alpha$ to
exist, the abstract domain must be **closed under meet** (else "the most precise element
covering $c$" may not exist — e.g. $\{0\}$ has no best abstraction in a domain lacking it).

## 4. Galois insertion & the closure view (peculiarities)
Abstraction generally loses precision, so $\gamma\circ\alpha\neq\mathrm{id}$. But
concretization should lose *nothing*, so we often want $\alpha\circ\gamma=\mathrm{id}$. When
it holds we have a **Galois insertion (= embedding)**.

> [!note] Galois insertion — three equivalent conditions
> A Galois connection is a **Galois insertion** iff any of:
> (1) $\alpha$ is **surjective**; (2) $\gamma$ is **injective**; (3) $\alpha\circ\gamma=\mathrm{id}$.
> Intuition: **no redundant abstract elements** — every abstract element is the best
> abstraction of its own meaning.

- **GI = "no spurious elements" — all three conditions are the same statement.** A
  **spurious** element $p$ is one that is **no set's best abstraction**; equivalently
  $p\notin\mathrm{image}(\alpha)$ ($\alpha$ not surjective), $\exists a'\sqsubset p$ with
  $\gamma(a')=\gamma(p)$ ($\gamma$ not injective), or $\alpha(\gamma(p))\neq p$
  ($\alpha\circ\gamma\neq\mathrm{id}$). Surjectivity is **not** the odd one out: since $\alpha$
  returns the *tightest* abstraction, a too-loose $p$ is simply never produced by $\alpha$.
- **Non-trivial GC-not-GI — the (non-reduced) Cartesian product** (see
  [10 §combining domains](10-abstract-domains-operators.md)). Intervals $\times$ Congruences is
  a GC (product of GCs), but **not** a GI: $([1,5],2\mathbb Z)$ and $([2,4],2\mathbb Z)$ both mean
  $\{2,4\}$ (and every $(\bot,\cdot)/(\cdot,\bot)$ means $\varnothing$), so $\gamma$ isn't
  injective and $([1,5],2\mathbb Z)$ is spurious ($\alpha(\{2,4\})=([2,4],2\mathbb Z)$). The
  **reduced product** collapses equal-$\gamma$ elements onto their tightest representative
  (the reduction $\rho=\alpha\circ\gamma$), restoring a GI. **Any GC reduces to a GI this way**,
  which is why "assume a GI" is w.l.o.g.
- **Closure-operator view.** Write $A(c)\triangleq\gamma(\alpha(c))$. This is an **upper
  closure operator**: **monotone, extensive, idempotent** ($A(A(c))=A(c)$). Its image
  $A(C)=\gamma(A)$ is the set of **expressible elements** ($c$ with $c=\gamma(\alpha(c))$).
  So an abstract domain can be identified with a **subset of the concrete domain** — no
  symbolic representation needed to reason about it.

## 5. Properties (why the Galois connection is exactly right)
- **Soundness for free.** $c\le\gamma(\alpha(c))$ means $\alpha$ never under-reports; every
  concrete element is covered by its abstraction. This is precisely the intro's soundness
  requirement, now guaranteed by the adjunction.
- **Optimal precision.** $\alpha(c)$ is not just *a* sound abstraction but the **best** one —
  the connection pins down a unique tightest abstract element per concrete element.
- **Preservation (a free theorem).** $\alpha$ preserves **joins**, $\gamma$ preserves **meets**:
  $\alpha(X\cup Y)=\alpha(X)\sqcup\alpha(Y)$, $\gamma(a\sqcap b)=\gamma(a)\cap\gamma(b)$ — and *only*
  these directions ($\gamma$ does **not** preserve joins: $\gamma([1,2]\sqcup[7,8])=\{1..8\}\neq\{1,2,7,8\}$,
  and that gap *is* the abstract join's imprecision). Two payoffs: **(i) abstract operators** —
  the concrete semantics merges by $\cup$ (branches) and $\cap$ (guards), so $\sqcup$/$\sqcap$ are
  their *faithful* abstract images and $f^\sharp=\alpha\circ f\circ\gamma$ composes soundly;
  **(ii) fixpoint transfer** — since $\mathrm{lfp}\,F=\bigsqcup_n F^n(\bot)$, $\alpha$ sliding through
  the join gives $\alpha(\mathrm{lfp}\,F)=\bigsqcup_n\alpha(F^n(\bot))\sqsubseteq\bigsqcup_n(F^\sharp)^n(\bot^\sharp)=\mathrm{lfp}\,F^\sharp$
  — the soundness theorem of the analysis ([11](11-abstract-analysis-fixpoints-widening.md)).
- **When there is no $\alpha$ (Convex Polyhedra — *not* a Galois insertion).** A GC requires
  $\alpha$ to be a **total** function returning the best abstraction of *every* set. For
  **Convex Polyhedra** this fails: a **disk has no smallest enclosing polyhedron** (any polygon
  can be tightened by another facet — no minimum), so $\alpha(\text{disk})$ **doesn't exist**.
  Hence polyhedra are **not a Galois connection at all** — and *a fortiori not a Galois insertion*
  (an insertion is a special GC). The framework instead uses **concretization alone** ($\gamma$-only):
  $\gamma:A\to C$ injective, soundness defined directly as $c\le\gamma(a)$, no $\alpha$, no adjunction.
  > [!warning] Common misconception
  > "$\gamma$ injective and $\alpha\circ\gamma=\mathrm{id}$" hold only on the sets that *already are*
  > polyhedra — but abstraction must handle *arbitrary* sets, where $\alpha$ breaks. And note a GI
  > needs $\alpha$ **surjective** (not "non-surjective"). So the non-total $\alpha$ is the disqualifier,
  > not evidence of an insertion.

## 6. Pros / cons / use cases
- **Pros:** a clean, reusable contract giving soundness **and** best precision; either map
  fixes the other; the closure view makes domains just "well-behaved subsets" of the concrete.
- **Cons:** requires a **best abstraction** to exist (closed under meet); some useful domains
  are $\gamma$-only; the theory is heavier than the intuition.
- **Use cases:** the mathematical foundation for designing sound abstract domains and
  operators ([10](10-abstract-domains-operators.md)) and for proving analyses correct via
  fixpoint transfer ([11](11-abstract-analysis-fixpoints-widening.md)).

---

## 📋 Cheatsheet (complete)

### Order theory
$$\text{poset }(X,\sqsubseteq);\quad \text{lub }\bigsqcup A\ (\sqcup),\ \text{glb }\sqcap A\ (\sqcap);\quad \text{complete lattice }(X,\sqsubseteq,\sqcup,\sqcap,\bot,\top)$$
$$\bot=\textstyle\bigsqcup\varnothing=\sqcap X,\quad \top=\sqcap\varnothing=\bigsqcup X;\qquad \textbf{ACC}:\ \text{no infinite ascending chain}\ \Rightarrow\ \text{analysis terminates}.$$

### Function properties
$$\text{monotone: } x\sqsubseteq y\Rightarrow f(x)\sqsubseteq f(y);\quad \text{continuous: preserves chain lubs};\quad \text{extensive: } a\sqsubseteq f(a);\quad \text{reductive: } f(a)\sqsubseteq a.$$

### Galois connection
$$(C,\le)\ \xrightleftharpoons[\alpha]{\gamma}\ (A,\sqsubseteq)\quad\overset{\triangle}{\iff}\quad \forall c,a:\ \alpha(c)\sqsubseteq a\ \Longleftrightarrow\ c\le\gamma(a).$$
$$\text{equivalently: }\ \underbrace{c\le\gamma(\alpha(c))}_{\text{sound (extensive)}}\ \wedge\ \underbrace{\alpha(\gamma(a))\sqsubseteq a}_{\text{reductive}},\ \text{both monotone.}$$
$$\alpha(c)=\textstyle\sqcap\{a\mid c\le\gamma(a)\}\ (\textbf{best abstraction}),\qquad \gamma(a)=\bigsqcup\{c\mid\alpha(c)\sqsubseteq a\}.$$
$\alpha$ preserves lubs; $\gamma$ preserves glbs. $\alpha$ exists $\Rightarrow$ domain closed under meet.

### Galois insertion (GI / embedding)
$$\text{GC is a GI} \iff \alpha\text{ surjective} \iff \gamma\text{ injective} \iff \alpha\circ\gamma=\mathrm{id}.$$
(No redundant abstract elements. GC-not-GI ⟹ some abstract value is "useless".)

### Closure-operator view
$$A\triangleq\gamma\circ\alpha:C\to C\ \text{ is monotone, extensive, idempotent (an upper closure)};\quad A(C)=\gamma(A)=\{\text{expressible elements}\}.$$

### When there is no $\alpha$
No best abstraction (e.g. Convex Polyhedra) $\Rightarrow$ no Galois connection $\Rightarrow$ work with $\gamma$ alone (concretization-only).
