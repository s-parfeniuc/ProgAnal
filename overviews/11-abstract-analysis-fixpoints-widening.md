---
title: Abstract Analysis — Fixpoints, Widening & Narrowing
abbrev: AI (analysis)
lectures: "12 (analysis as fixpoint), 14 (convergence), 15 (Abstract Analysis)"
paper: "Cousot & Cousot, POPL 1977 (widening/narrowing); A. Miné, Tutorial (reading)"
theme: "running the analysis: abstract stores, abstract fixpoints, soundness by fixpoint transfer, termination by widening"
oneliner: "An analysis lifts a value domain to abstract stores and computes lfp F♯; soundness is fixpoint transfer α(lfp F) ⊑ lfp F♯, termination is bought with widening ∇ and precision recovered with narrowing △."
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
$$\text{reachable} = \mathrm{lfp}\ \lambda X.\ S_0\cup[\![  c ]\!] X \qquad(\text{by Kleene: } \textstyle\bigcup_{k\ge 0}(\lambda X.\dots)^k(\varnothing)).$$
This **strongest invariant is not computable in general**. The **abstract interpreter**
mirrors the concrete one construct-by-construct on the abstract domain:
$$[\![  c_1;c_2 ]\!]^\sharp=[\![  c_2 ]\!]^\sharp\circ[\![  c_1 ]\!]^\sharp,\quad [\![  c_1{+}c_2 ]\!]^\sharp=[\![  c_1 ]\!]^\sharp\sqcup[\![  c_2 ]\!]^\sharp,\quad [\![  c^\star ]\!]^\sharp=\lambda S.\ \mathrm{lfp}\ \lambda X.\ S\sqcup[\![  c ]\!]^\sharp X.$$
The analysis result at a loop is $\mathrm{lfp}\,F^\sharp$, computed by **Kleene iteration**
$\bot\sqsubseteq F^\sharp(\bot)\sqsubseteq F^\sharp{}^2(\bot)\sqsubseteq\dots$ The **take-home**:
the whole interpreter is *induced by the atomic operations* — pick the domain and its atomic
transfer functions ([10](10-abstract-domains-operators.md)), and the analysis of every
compound command is fixed.

## 3. Building the abstract state — stores, liftings, products
A value domain ($A_1$ = Signs, Intervals, Congruences…) abstracts **one number**. Real
programs have **many variables**, and useful analyses **combine properties**. Three lattice
constructions build the abstract state we actually iterate on; each **derives a new lattice
(and a Galois connection) from old ones**, componentwise.

### 3a. Point-wise lifting (one lattice, indexed by variables)
Given a lattice $(L_1,\sqsubseteq_1,\dots)$ and a set $X$ (the variables), the **point-wise
lifting** is the function space $L\triangleq X\to L_1$ with **everything defined
argument-by-argument**:
$$f\sqsubseteq g \iff \forall x.\ f(x)\sqsubseteq_1 g(x),\quad (f\sqcup g)=\lambda x.\ f(x)\sqcup_1 g(x),\quad \bot=\lambda x.\bot_1,\ \top=\lambda x.\top_1.$$
This is exactly how one value domain becomes a map $x\mapsto$ (abstract value). It permits
"mixed" states like $\{x\mapsto\bot_1,\ y\mapsto l\}$ (one variable is $\bot$, others are not).

**Smashed** point-wise lifting collapses any function that is $\bot_1$ *somewhere* to the
single global bottom $\lambda x.\bot_1$:
$$L = (X\to(L_1\setminus\{\bot_1\}))\ \uplus\ \{\lambda x.\bot_1\}.$$
So the only way to be $\bot$ on one variable is to be $\bot$ **everywhere**. This matches the
concrete intuition that *if any variable can take no value, the whole state is unreachable*
($\varnothing$): e.g. on Intervals a smashed store is **either non-empty for every variable,
or the empty interval for all**. The concretization is $\gamma(f)=\lambda x.\ \gamma_1(f(x))$.

### 3b. Cartesian product (two lattices, side by side)
Given lattices $L_1,L_2$, the **Cartesian product** $L\triangleq L_1\times L_2$ orders and
joins **componentwise**:
$$(a_1,a_2)\sqsubseteq(b_1,b_2)\iff a_1\sqsubseteq_1 b_1\wedge a_2\sqsubseteq_2 b_2,\quad (a_1,a_2)\sqcup(b_1,b_2)=(a_1\sqcup_1 b_1,\ a_2\sqcup_2 b_2),\quad \bot=(\bot_1,\bot_2),\ \dots$$
The **product of two Galois connections is a Galois connection** with
$\gamma(a_1,a_2)=\gamma_1(a_1)\cap\gamma_2(a_2)$ — it tracks a **conjunction** of the two
properties. Canonical use: Intervals $\times$ Congruences, e.g. $([0,100],\,2\mathbb Z)$ means
"$0\le x\le 100$ **and** $x$ even" $=\{0,2,4,\dots,100\}$.

**Reduced product** fixes the plain product's defect: $\gamma$ is **not injective** —
several distinct pairs mean the same concrete set, e.g. $([1,5],2\mathbb Z)$ and
$([2,4],2\mathbb Z)$ both denote $\{2,4\}$, and $(\bot,2\mathbb Z)$, $([2,4],\bot)$,
$(\bot,\bot)$ all denote $\varnothing$. The reduced product **quotients by "equal
concretization"**, $(a_1,a_2)\equiv(b_1,b_2)\iff\gamma(a_1,a_2)=\gamma(b_1,b_2)$, and keeps
the **most precise representative** of each class. This restores an injective $\gamma$ (a
Galois insertion) and, crucially, lets the components **refine each other** — the interval
part can tighten the congruence part and vice-versa (see [10 §6](10-abstract-domains-operators.md)).

### 3c. Abstract stores (putting it together)
The concrete domain of a multi-variable program is $\wp(\Sigma)$, sets of stores
$\sigma:X\to\mathbb Z$. Abstracting it is **two abstractions composed** (GC∘GC = GC):
1. **Cartesian abstraction** $\wp(X\to\mathbb Z)\to (X\to\wp(\mathbb Z))$, i.e.
   $\gamma(\rho)=\{\sigma\mid\forall x.\ \sigma(x)\in\rho(x)\}$. This records, per variable,
   *which values it can take*, but **loses all relational information** (correlations between
   variables). E.g. $\rho=[x\mapsto\{0,5\},\,y\mapsto\{0,3\}]$ concretizes to **all four**
   combinations $\{[0,0],[0,3],[5,0],[5,3]\}$, so it cannot remember that $x{=}0$ went with
   $y{=}0$. This is why non-relational domains need Octagons/Polyhedra when correlations matter.
2. **Point-wise lifting of the value domain** $(X\to\wp(\mathbb Z))\to(X\to A_1)$ via §3a,
   $\gamma(\rho^\sharp)=\lambda x.\ \gamma_1(\rho^\sharp(x))$ — e.g.
   $[x\mapsto[0,5],\,y\mapsto[0,3]]$ over Intervals.

So an **abstract store is a map $X\to A_1$**; the analysis iterates the abstract interpreter
over these maps.

## 4. Soundness: the fixpoint transfer theorem
> [!important] Fixpoint transfer (why the analysis is sound)
> If $F$ is monotone and $F^\sharp$ is a **sound** abstraction of $F$ (i.e. $\alpha\circ F\sqsubseteq F^\sharp\circ\alpha$, see [10](10-abstract-domains-operators.md)), then
> $$\alpha\big(\mathrm{lfp}\,F\big)\ \sqsubseteq\ \mathrm{lfp}\,F^\sharp \qquad\Big(\text{equivalently } \mathrm{lfp}\,F\ \le\ \gamma(\mathrm{lfp}\,F^\sharp)\Big).$$
> The **abstract fixpoint over-approximates the concrete one** — soundness lifts from single
> operators (via each $F^\sharp$) to the whole least fixpoint. This is the theorem that makes
> the analysis trustworthy.

## 5. The termination problem — widening $\nabla$
Kleene iteration terminates iff the abstract domain satisfies the **Ascending Chain
Condition** (ACC): no infinite strictly-increasing chain. Many useful domains are **not** ACC
— e.g. **Intervals**: iterating a loop that grows a counter yields
$[0,0]\sqsubseteq[0,1]\sqsubseteq[0,2]\sqsubseteq\dots$ forever, never reaching the fixpoint.
(Congruences, by contrast, *are* effectively ACC: moving up loses modular constraints, which
shrinks the modulus $a$, and $a$ cannot shrink forever — $6\mathbb Z\sqsubset3\mathbb Z\sqsubset1\mathbb Z$.)
Cousot & Cousot's fix is a **widening operator** $\nabla$ that **extrapolates** to a
post-fixpoint in finitely many steps.

> [!note] Widening $\nabla:A\times A\to A$ — definition
> (i) **Covers** its arguments (so it over-approximates the join): $a\sqsubseteq a\nabla b$ and $b\sqsubseteq a\nabla b$, hence $a\sqcup b\sqsubseteq a\nabla b$.
> (ii) **Enforces termination:** for *any* increasing sequence $x_0\sqsubseteq x_1\sqsubseteq\dots$,
> the *widened* sequence $y_0=x_0,\ y_{i+1}=y_i\nabla x_{i+1}$ **stabilises** after finitely many steps.
>
> The loop is then computed as $\llbracket c^\star\rrbracket^\sharp=\lambda S.\ \mathrm{lfp}\ \lambda X.\ S\,\nabla\,\llbracket c\rrbracket^\sharp X$ — the iterates jump to a **stable over-approximation** (a post-fixpoint) instead of climbing forever. Widening **loses precision** to buy termination.

**Interval widening** (the canonical instance): **unstable bounds are pushed to infinity**,
$$[a,b]\ \nabla\ [a',b']\ =\ [\,(a'<a)\,?\,-\infty:a,\ \ (b'>b)\,?\,+\infty:b\,].$$
(The **naive widening** $x\nabla y = x$ if $y\sqsubseteq x$ else $\top$ works on any domain
with a $\top$, but jumps straight to $\top$ — maximally imprecise.) Two standard precision
knobs on top: **widening with delay** (do $k$ exact $\sqcup$ steps before switching to
$\nabla$) and **widening with thresholds** (extrapolate to the next value in a fixed set —
e.g. a guard constant — instead of all the way to $\infty$).

## 6. Recovering precision — narrowing $\triangle$
Widening overshoots (often to $[-\infty,+\infty]$ on one side). A **narrowing operator**
$\triangle$ then runs a **decreasing** iteration from the post-fixpoint, tightening the
result **without going below the concrete fixpoint** and still terminating.

> [!note] Narrowing $\triangle:A\times A\to A$ — definition
> (i) **Stays in between:** if $b\sqsubseteq a$ then $b\sqsubseteq a\triangle b\sqsubseteq a$
> (it refines $a$ using $b$ but never drops below $b$ — so it cannot fall under the fixpoint).
> (ii) **Enforces termination** of decreasing iterations $z_0=x^\nabla,\ z_{i+1}=z_i\triangle F^\sharp(z_i)$.

**Interval narrowing:** refine only the infinite bounds introduced by widening,
$$[a,b]\ \triangle\ [a',b']\ =\ [\,(a=-\infty)\,?\,a':a,\ \ (b=+\infty)\,?\,b':b\,].$$
(A finite bound is trusted and kept; an $\pm\infty$ bound is replaced by the freshly-computed
one.) Typical loop analysis: **iterate up with $\nabla$ to a post-fixpoint, then iterate down
with $\triangle$** to sharpen it. Narrowing can recover a finite bound but generally **not**
the least fixpoint.

## 7. The loop in practice — the iteration algorithm and worked traces
### 7a. The algorithm (label-wise chaotic iteration)
Both concrete and abstract analyses are the same worklist loop, just with $\cup\to\sqcup$ and
(for acceleration) $\sqcup\to\nabla$:
```
S♯ ← ⊥
repeat
    R♯ ← S♯
    S♯ ← S♯ ⊔ F♯(S♯)          -- plain: ⊔ ;  accelerated: ∇
until S♯ ⊑ R♯                  -- fixpoint / post-fixpoint reached (checked label-wise)
return R♯
```
The `⊑` test detects when the iterates **stop growing**. Without acceleration this halts only
on an ACC domain; with $\nabla$ at loop heads it halts on any domain (then a $\triangle$ pass
sharpens). The **accelerated abstract interpreter** is *exactly* the abstract interpreter with
$\sqcup$ replaced by $\nabla$ at loops.

### 7b. Worked interval trace — `x:=0; while x<40 do x:=x+1`
Loop-head functional $F^\sharp(I)=[0,0]\,\sqcup\,\llbracket x{:=}x{+}1\rrbracket^\sharp\big(\llbracket x{<}40\rrbracket^\sharp I\big)$.

*Plain Kleene* diverges: $[0,0]\sqsubseteq[0,1]\sqsubseteq[0,2]\sqsubseteq\dots$ (Intervals ¬ACC).

*Widening phase* $X_{i+1}=X_i\,\nabla\,F^\sharp(X_i)$:

| $i$ | $X_i$ | $F^\sharp(X_i)$ | $X_{i+1}=X_i\nabla F^\sharp(X_i)$ |
|---|---|---|---|
| 0 | $\bot$ | $[0,0]$ | $[0,0]$ |
| 1 | $[0,0]$ | $[0,0]\sqcup[1,1]=[0,1]$ | $[0,0]\nabla[0,1]=[0,+\infty]$ |
| 2 | $[0,+\infty]$ | $[0,0]\sqcup[1,40]=[0,40]$ | $[0,+\infty]\nabla[0,40]=[0,+\infty]$ ✓ stable |

Post-fixpoint: $x\in[0,+\infty]$ at the head — sound but imprecise.

*Narrowing phase* $Z_{i+1}=Z_i\,\triangle\,F^\sharp(Z_i)$:

| $i$ | $Z_i$ | $F^\sharp(Z_i)$ | $Z_{i+1}$ |
|---|---|---|---|
| 0 | $[0,+\infty]$ | $[0,0]\sqcup[1,40]=[0,40]$ | $[0,+\infty]\triangle[0,40]=[0,40]$ |
| 1 | $[0,40]$ | $[0,0]\sqcup[1,40]=[0,40]$ | $[0,40]$ ✓ stable |

Sharpened head invariant $x\in[0,40]$; after the loop (guard negation $x\ge40$) we get
$x\in[40,40]$, i.e. **$x=40$** — the exact result, recovered.

### 7c. Reading the invariant off the loop
The "loop invariant" is precisely the **abstract value stabilised at the loop head**: the
$\sqsubseteq$-least (post-)fixpoint of $\lambda X.\,S\sqcup\llbracket\text{body}\rrbracket^\sharp X$.
It is **inferred, not supplied** — unlike Hoare logic, no human invariant is needed: the
iteration *computes* it by repeatedly executing the body abstractly and joining, until the
join adds nothing new (a post-fixpoint is inductive: re-running the body cannot leave it). The
domain decides *what shape* of invariant is expressible (bounds → Intervals; alignment/parity
→ Congruences), and widening decides *how coarsely* the head is over-approximated.

### 7d. Congruence example (why the modulus is a `gcd`)
```
X := 0; Y := 2;
while X < 40 do
    X := X + 2;
    if X < 5 then Y := Y + 18 endif;
    if X > 8 then Y := Y - 30 endif
done
```
Inferred loop invariant: **$X\in 2\mathbb Z+0$** ($X$ even) and **$Y\in 6\mathbb Z+2$**.
Reading it: except when an abstract value is a singleton, a test like $X<40$ or $X>8$ carries
**no congruence information**, so it abstracts to the **identity** — the analysis cannot use
the guards to prune, it must be sound for *both* branches. Hence at each iteration $Y$ may be
incremented by $18$ **or** decremented by $30$; the congruence join of these two possibilities
has modulus $\gcd(18,30)=6$, and starting from $Y=2$ the offset stays $2\bmod 6$, giving
$Y\in6\mathbb Z+2$. $X$ starts even and only ever gets $+2$, so it stays in $2\mathbb Z$.
This is the payoff of the Congruence domain: it proves **alignment/parity** invariants
(useful for array-stride and pointer-offset checks) that Intervals cannot express.

## 8. Properties (soundness & termination) + the accelerated interpreter
- **Soundness:** guaranteed by the **fixpoint transfer theorem** (§4), provided each abstract
  operator is sound (§[10](10-abstract-domains-operators.md)); the widened/narrowed result is
  a **sound post-fixpoint**, still $\sqsupseteq\alpha(\mathrm{lfp}\,F)$.
- **Termination:** guaranteed either by an **ACC** domain (plain Kleene) or by **widening**
  (non-ACC domains). Narrowing's decreasing iteration also terminates.
- **Precision/cost knobs:** the domain (see [10](10-abstract-domains-operators.md)), the
  **widening delay** (do $k$ exact steps before widening), **widening thresholds**, and the
  **narrowing** passes.
- The **accelerated abstract interpreter** is just the abstract interpreter with $\sqcup$
  replaced by $\nabla$ at loops (then a $\triangle$ pass).
- **Precision is *intensional*** (depends on how the program is *written*, not just what it
  computes): two concretely-equivalent commands can have **different** abstract results
  (e.g. `while x>0 do x:=x-1` gives $[0,0]$ but the equivalent `while x>1 do x:=x-2` gives
  $[0,1]$ on Intervals). So abstract equivalence $\sim$ and concrete equivalence $\approx$ are
  incomparable — neither implies the other.

## 9. Pros / cons / use cases
- **Pros:** a general, **automatic** recipe to compute sound invariants for **any** sound
  domain, **even without ACC**; **no human-supplied invariants** (contrast Hoare logic);
  precision is tunable (domain, widening delay/thresholds, narrowing); products/liftings build
  the abstract-store domain modularly.
- **Cons:** widening is **non-monotone** and its design is delicate (a bad $\nabla$ can wreck
  precision); results are **post-fixpoints**, generally not the best abstraction; the Cartesian
  store abstraction **loses relational info**, and precision is **intensional**.
- **Use cases:** the engine inside every abstract-interpretation analyser (Astrée, etc.) —
  loop-invariant inference, bounds/overflow/division-by-zero/array-safety proofs, alignment
  (Congruences).

---

## 📋 Cheatsheet (complete)

### Analysis = fixpoint
$$\text{concrete reachable} = \mathrm{lfp}\ \lambda X.\ S_0\cup\llbracket c\rrbracket X\ \ (\text{strongest invariant, uncomputable});\qquad \text{analysis} = \mathrm{lfp}\,F^\sharp.$$
Abstract interpreter: $\llbracket c_1;c_2\rrbracket^\sharp=\llbracket c_2\rrbracket^\sharp\circ\llbracket c_1\rrbracket^\sharp$, $\ \llbracket c_1{+}c_2\rrbracket^\sharp=\llbracket c_1\rrbracket^\sharp\sqcup\llbracket c_2\rrbracket^\sharp$, $\ \llbracket c^\star\rrbracket^\sharp=\lambda S.\ \mathrm{lfp}\ \lambda X.\ S\sqcup\llbracket c\rrbracket^\sharp X$.
Kleene: $\mathrm{lfp}\,F^\sharp=\bigsqcup_{k\ge 0}(F^\sharp)^k(\bot)$ (terminates iff ACC).

### Building the abstract state
$$\text{Point-wise: } L=X\to L_1\ \text{(componentwise)};\quad \text{Smashed: } (X\to(L_1{\setminus}\{\bot_1\}))\uplus\{\lambda x.\bot_1\}\ (\bot\text{ on one}\Rightarrow\bot\text{ everywhere}).$$
$$\text{Cartesian }A_1\times A_2:\ \gamma(a_1,a_2)=\gamma_1(a_1)\cap\gamma_2(a_2)\ \text{(conjunction)};\quad \text{Reduced}=\text{quotient by equal-}\gamma\ (\text{GI; components refine}).$$
$$\text{Abstract store }X\to A_1 = \underbrace{\wp(X{\to}\mathbb Z)\to(X{\to}\wp(\mathbb Z))}_{\text{Cartesian abstr., loses relational info}}\ \circ\ \underbrace{(X{\to}\wp(\mathbb Z))\to(X{\to}A_1)}_{\text{point-wise lift of }A_1}.$$

### Soundness — fixpoint transfer
$$F\text{ monotone},\ \alpha\circ F\sqsubseteq F^\sharp\circ\alpha\ \Longrightarrow\ \alpha(\mathrm{lfp}\,F)\sqsubseteq\mathrm{lfp}\,F^\sharp\ \Longleftrightarrow\ \mathrm{lfp}\,F\le\gamma(\mathrm{lfp}\,F^\sharp).$$

### Widening $\nabla$ (termination for non-ACC domains)
$$a\sqsubseteq a\nabla b,\quad b\sqsubseteq a\nabla b;\qquad y_0=x_0,\ y_{i+1}=y_i\nabla x_{i+1}\ \text{stabilises for every increasing }(x_i).$$
$$\llbracket c^\star\rrbracket^\sharp=\lambda S.\ \mathrm{lfp}\ \lambda X.\ S\,\nabla\,\llbracket c\rrbracket^\sharp X;\qquad [a,b]\nabla[a',b']=[\,a'<a?\,{-\infty}:a,\ b'>b?\,{+\infty}:b\,].$$

### Narrowing $\triangle$ (recover precision)
$$b\sqsubseteq a\ \Rightarrow\ b\sqsubseteq a\triangle b\sqsubseteq a;\quad\text{decreasing iteration terminates};\qquad [a,b]\triangle[a',b']=[\,a{=}{-\infty}?\,a':a,\ b{=}{+\infty}?\,b':b\,].$$
Recipe: iterate up with $\nabla$ to a post-fixpoint, then down with $\triangle$.

### Loop iteration algorithm
$$S^\sharp\!\leftarrow\!\bot;\ \textbf{repeat}\ R^\sharp\!\leftarrow\!S^\sharp;\ S^\sharp\!\leftarrow\!S^\sharp\ \{\sqcup\mid\nabla\}\ F^\sharp(S^\sharp)\ \textbf{until}\ S^\sharp\sqsubseteq R^\sharp;\ \textbf{return}\ R^\sharp.$$
Invariant = value stabilised at the loop head (**inferred**, not supplied). Precision is **intensional** ($\approx\not\Rightarrow\sim$ and $\sim\not\Rightarrow\approx$).

### Worked traces
$$\text{Intervals, }x{:=}0;\text{while }x{<}40\text{ do }x{:=}x{+}1:\quad \nabla:\ \bot\to[0,0]\to[0,+\infty]\ \checkmark;\quad \triangle:\ [0,+\infty]\to[0,40]\ \checkmark;\quad \text{exit }x{=}40.$$
$$\text{Congruences, }X{:=}0;Y{:=}2;\text{loop}(+18/{-}30):\quad X\in2\mathbb Z{+}0,\ Y\in6\mathbb Z{+}2\ (6=\gcd(18,30);\text{ guards}\to\text{id}).$$

### Termination summary
$$\text{ACC domain}\Rightarrow\text{plain Kleene terminates};\qquad \text{non-ACC (e.g. Intervals, Polyhedra)}\Rightarrow\text{use }\nabla\ (+\ \triangle).\quad \text{Congruences: eff. ACC (modulus shrinks, }6\mathbb Z\sqsubset3\mathbb Z\sqsubset1\mathbb Z).$$
