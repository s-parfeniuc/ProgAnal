---
title: Abstract Domains & Operators
abbrev: AI (domains)
lectures: "12 (abstract operations), 14 (Abstract Domains), 15 (domains & products)"
paper: "A. Miné, Tutorial on Static Inference of Numeric Invariants (reading); Cousot & Cousot 1979 (reduced product)"
theme: "concrete numeric domains + sound abstract operators (transfer functions)"
oneliner: "Give each concrete operation a sound abstract counterpart; the best one is f♯ = α∘f∘γ."
render: "Notation is LaTeX math ($…$ / $$…$$). Preview with a KaTeX markdown extension."
---

# Abstract Domains & Operators

**Theme:** the concrete numeric domains, and how to give each concrete operation a **sound abstract counterpart** (a *transfer function*). Builds on the Galois machinery of [09](09-order-theory-galois-connections.md); feeds the fixpoint analysis of [11](11-abstract-analysis-fixpoints-widening.md).

## 1. Purpose & core idea
An abstract domain is only useful if we can **compute** in it. For every concrete operation
$F$ (add, multiply, guard, assignment…) we need an abstract operation $F^\sharp$ that
mirrors it **soundly** on abstract elements. The design goal: $F^\sharp$ should over-cover
what $F$ does, and ideally do so as **precisely** as the domain allows.

## 2. Transfer functions & sound abstract operators
A **transfer function** says how the abstract state changes after an instruction. For a
concrete operator $F:C\to C$ we define $F^\sharp:A\to A$ and require **soundness**:

> [!important] Sound abstract operator (three equivalent forms)
> $$F^\sharp\text{ sound for }F \iff \underbrace{F(\gamma(a))\subseteq\gamma(F^\sharp(a))}_{\text{concretize then run}\subseteq \text{run then concretize} } \iff \alpha\circ F\circ\gamma\ \sqsubseteq\ F^\sharp \iff \alpha\circ F\ \sqsubseteq\ F^\sharp\circ\alpha.$$
> (The equivalences use the Galois biconditional $c\le\gamma(a)\iff\alpha(c)\sqsubseteq a$.)

Lifted to $n$-ary operations: if each $a_i$ soundly abstracts $v_i$, then
$F^\sharp(a_1,\dots,a_n)$ must soundly abstract $F(v_1,\dots,v_n)$.

## 3. Best correct approximation (BCA)
Among all sound $F^\sharp$, there is a **most precise** one — the **best correct
approximation**:
$$F^\sharp_{\mathrm{bca}}\ \triangleq\ \alpha\circ F\circ\gamma.$$
Every sound $F^\sharp$ satisfies $F^\sharp\sqsupseteq\alpha\circ F\circ\gamma$, so the BCA is
the tightest possible abstract operator (it does the concrete op on the *meaning*, then
takes the best abstraction). **Caveat — BCAs don't compose:** $\mathrm{bca}(F)\circ\mathrm{bca}(G)$
is sound but generally **not** the BCA of $F\circ G$ (precision is lost at each step), which
is one root cause of analysis imprecision.

## 4. Soundness vs completeness of operators (the rule of signs)
The classic example is the **sign domain** $A=\{\mathbb Z_{<0},\mathbb Z_{=0},\mathbb Z_{>0}\}$
(Brahmagupta's *rule of signs*, 628 AD) with abstract multiplication $\times^\sharp$:

$$\mathbb Z_{>0}\times^\sharp\mathbb Z_{<0}=\mathbb Z_{<0},\quad \mathbb Z_{=0}\times^\sharp a=\mathbb Z_{=0},\quad \mathbb Z_{<0}\times^\sharp\mathbb Z_{<0}=\mathbb Z_{>0},\ \dots$$

- **Correctness (soundness)** — for any expression $e$: $\sigma(e)=\mathbb Z_{>0}\Rightarrow[\![  e ]\!]>0$ (etc.), by structural induction. The abstract answer never lies.
- **Completeness** — the converse $[\![  e ]\!]>0\Rightarrow\sigma(e)=\mathbb Z_{>0}$: the abstract computation loses **no** precision relative to the domain. Formally $F^\sharp$ is **(exactly) complete** when $\alpha\circ F=F^\sharp\circ\alpha$ (equality, not just $\sqsubseteq$). Sign-multiplication is complete; **sign-addition is *not*** (e.g. $\mathbb Z_{>0}+^\sharp\mathbb Z_{<0}=\top$), and $|\cdot|$ is not complete on Intervals — completeness is domain- and operator-specific.

## 5. The abstract domains
| Domain | Abstract element $a$ | $\gamma(a)$ | Rel.? | ACC? |
|---|---|---|---|---|
| **Signs** | sign class per variable | half-lines | no | yes |
| **Constants** | $\{c\}$ or $\top/\bot$ | a single value | no | yes |
| **Intervals** | $[l,u]$, $l\in\mathbb Z\cup\{-\infty\}$, $u\in\mathbb Z\cup\{+\infty\}$ | $\{x\mid l\le x\le u\}$ | no | **no** |
| **Congruences** | $a\mathbb Z+b$ | $\{an+b\mid n\in\mathbb Z\}$ | no | varies |
| **Octagons** | $\pm x\pm y\le c$ | a "diamond" region | yes | no |
| **Convex polyhedra** | $\bigwedge_i (c_ix+d_iy\le e_i)$ | a polyhedron | yes | **no**; **no BCA** |

Intervals: lub $[a,b]\sqcup[a',b']=[\min(a,a'),\max(b,b')]$ (smallest enclosing interval),
glb $=$ intersection. **Convex polyhedra have no best abstraction** (a curved set has no
smallest enclosing polyhedron) — so no Galois connection, only a $\gamma$
(see [09 §5](09-order-theory-galois-connections.md)).

**Abstract stores.** To analyse programs with several variables, lift a value domain to
**stores** $X\to A$ **point-wise** (each variable independently — this is itself a
*Cartesian* abstraction and loses relational info); a *smashed* lifting collapses any store
containing $\bot$ to a single $\bot$.

## 6. Combining domains (deriving new lattices)
- **Composition of Galois connections is a Galois connection** ($\gamma=\gamma_1\circ\gamma_2$, $\alpha=\alpha_2\circ\alpha_1$) — abstractions stack.
- **Cartesian product** $A_1\times A_2$: componentwise order$\lub\glb$ $\bot$/$\top$; the
  product of two GCs is a GC with $\gamma(a_1,a_2)=\gamma_1(a_1)\cap\gamma_2(a_2)$. Lets one
  analysis track **conjunctive** properties (e.g. Intervals $\times$ Congruences:
  $([0,100],2\mathbb Z)$ means "even, $0..100$").
- **Reduced product** fixes the product's flaw that $\gamma$ is **not injective** — e.g.
  $([1,5],2\mathbb Z)$ and $([2,4],2\mathbb Z)$ both mean $\{2,4\}$; several pairs mean
  $\varnothing$. The reduced product **quotients** by "same concretization" (keeping the most
  precise representative), restoring a Galois insertion and letting the components **refine
  each other**.

## 7. Pros / cons / use cases
- **Pros:** a menu of domains trading precision for cost; the BCA gives a canonical tightest
  operator; products/reduced products build rich domains modularly.
- **Cons:** BCAs don't compose (precision drift); relational domains (polyhedra) are
  expensive and may lack a BCA; completeness is rare and operator-specific.
- **Use cases:** choosing/engineering the domain for a target property (bounds → Intervals;
  alignment → Congruences; linear relations → Octagons/Polyhedra), then running the fixpoint
  analysis of [11](11-abstract-analysis-fixpoints-widening.md).

---

## 📋 Cheatsheet (complete)

### Sound abstract operator (transfer function)
$$F^\sharp\text{ sound} \iff F\circ\gamma\ \subseteq\ \gamma\circ F^\sharp \iff \alpha\circ F\circ\gamma\ \sqsubseteq\ F^\sharp \iff \alpha\circ F\ \sqsubseteq\ F^\sharp\circ\alpha.$$
$n$-ary: $a_i$ sound for $v_i\ \Rightarrow\ F^\sharp(a_1,\dots,a_n)$ sound for $F(v_1,\dots,v_n)$.

### Best correct approximation
$$F^\sharp_{\mathrm{bca}}=\alpha\circ F\circ\gamma;\qquad \forall\text{ sound }F^\sharp:\ F^\sharp\sqsupseteq\alpha\circ F\circ\gamma.\qquad \textbf{BCAs do not compose.}$$

### Completeness of an operator (exactness)
$$F^\sharp\text{ complete} \iff \alpha\circ F=F^\sharp\circ\alpha\ \ (\text{equality}).\quad \text{sign-}\times \text{ complete; sign-}+ \text{ and } |\cdot|_{\mathrm{Int}} \text{ not.}$$

### Rule of signs (multiplication table, $A=\{\mathbb Z_{<0},\mathbb Z_{=0},\mathbb Z_{>0}\}$)
$$\times^\sharp:\quad {>}\cdot{>}={>},\ {>}\cdot{<}={<},\ {<}\cdot{<}={>},\ {=}\cdot a={=}.\quad\text{Correct }(\Rightarrow)\text{ and complete }(\Leftarrow)\text{ by structural induction.}$$

### Domains (precision ↑, cost ↑)
$$\text{Signs}\subsetneq\text{Intervals}\subsetneq\text{Octagons}\subsetneq\text{Polyhedra};\quad \text{Congruences }a\mathbb Z+b\text{ orthogonal};\quad \text{Intervals: }[a,b]\sqcup[a',b']=[\min(a,a'),\max(b,b')].$$
Polyhedra: no BCA / no Galois connection ($\gamma$-only). Stores: $X\to A$ point-wise (Cartesian) lift.

### Combining domains
$$\text{GC}\circ\text{GC}=\text{GC};\qquad \text{Cartesian }A_1\times A_2:\ \gamma(a_1,a_2)=\gamma_1(a_1)\cap\gamma_2(a_2)\ \text{(componentwise lattice)};$$
$$\text{Reduced product} = \text{Cartesian product quotiented by equal-}\gamma\ (\text{restores injective }\gamma\text{ / GI; components refine each other}).$$
