# Proofs — Control Flow Analysis (0-CFA for FUN · metatheory · constraints · k-CFA · CFA for π)

> Every theorem/lemma/counterexample **proved on the slides** of lectures 17–23,
> `CFA-for-FUN` and `CFA-for-Pi`. Statement first, then the proof as the slides give it.
> Source `[CFA-FUN / slide M]`, `[CFA-Pi / slide M]` (the consolidated decks; the numbered
> lectures 18–23 reuse the same slides). Importance: **★★★** core · **★★** secondary ·
> **★** minor / stated-without-proof.
> See [`../overviews/13`–`19`](../overviews/README.md) and
> [`../exercises/EX-03-control-flow-analysis.md`](../exercises/EX-03-control-flow-analysis.md).

Notation: an analysis **result** is a pair `(Ĉ, ρ̂)` — `Ĉ : Lab → ℘(Term)` the *abstract
cache* (which function abstractions may flow to each label) and `ρ̂ : Var → ℘(Term)` the
*abstract environment*. `(Ĉ, ρ̂) ⊧ e` = "the guess is **acceptable** for `e`";
`⊧s` = syntax-directed variant; `⊧c` = constraint-based variant.

---

## 1. Semantic correctness of 0-CFA — `CFA-for-FUN`

### CFA.P1 Subject reduction (semantic correctness of 0-CFA)  `[CFA-FUN / slide 93–98]` ★★★
**Th.** If `ρ R ρ̂` and `ρ ⊢ ie → ie′` then `(Ĉ, ρ̂) ⊧ ie` implies `(Ĉ, ρ̂) ⊧ ie′`.
*(«All acceptable analysis results remain acceptable under evaluation» — CFA predictions
are **stable under evaluation**, so whatever the program actually computes was already
predicted.)*

**The correctness relations** `[slide 91–92]`. A concrete value is a **closure**
`v = Close t in ρ`, so correctness must be defined **mutually recursively** on values and
environments:
```
v V (ρ̂, v̂)   iff   ∀t ∀ρ.  (v = Close t in ρ)  ⟹  ( t ∈ v̂  ∧  ρ R ρ̂ )
ρ R ρ̂        iff   dom(ρ) ⊆ dom(ρ̂)  ∧  ∀x ∈ dom(ρ). ρ(x) V (ρ̂, ρ̂(x))
```
i.e. the abstract environment must over-approximate every concrete closure **and, recursively,
every environment those closures capture**.

**Proof.** Assume `ρ R ρ̂` and `ρ ⊢ ie → ie′`; prove `(Ĉ, ρ̂) ⊧ ie′` **by induction on the
structure of the inference tree** for `ρ ⊢ ie → ie′`.

- **`[var]`**: `ρ ⊢ xˡ → vˡ` with `v = ρ(x)`.
  If `v = c` (a constant) there is nothing to prove. If `v = Close t₀ in ρ₀`:
  from `ρ R ρ̂` we get `v V (ρ̂, ρ̂(x))`, hence `t₀ ∈ ρ̂(x)` and `ρ₀ R ρ̂`;
  from `(Ĉ, ρ̂) ⊧ ie` (clause `[var]`: `ρ̂(x) ⊆ Ĉ(l)`) we get `t₀ ∈ Ĉ(l)`.
  With `t₀ ∈ Ĉ(l)` and `ρ₀ R ρ̂` the clause `[close]` gives `(Ĉ, ρ̂) ⊧ ie′`. ✔
  *(The value was **already predicted** by the analysis.)*

- **`[fn]`**: `ρ ⊢ (fn x => e₀)ˡ → (Close (fn x => e₀) in ρ₀)ˡ` with `ρ₀ = ρ|FV(fn x => e₀)`.
  From `(Ĉ, ρ̂) ⊧ ie` (clause `[fn]`) we get `{fn x => e₀} ⊆ Ĉ(l)`; from `ρ R ρ̂` we
  immediately get `ρ₀ R ρ̂` (a restriction of a correct environment is correct). Clause
  `[close]` then gives `(Ĉ, ρ̂) ⊧ ie′`. ✔ *(The abstraction is already recorded in `Ĉ(l)`.)*

- **`[app1]`** (evaluate the operator): `ρ ⊢ (ie₁ ie₂)ˡ → (ie′₁ ie₂)ˡ` because `ρ ⊢ ie₁ → ie′₁`.
  The induction hypothesis applied to `(Ĉ, ρ̂) ⊧ ie₁`, `ρ R ρ̂`, `ρ ⊢ ie₁ → ie′₁` yields
  `(Ĉ, ρ̂) ⊧ ie′₁`, which suffices for `(Ĉ, ρ̂) ⊧ (ie′₁ ie₂)ˡ`. ✔ (`[app2]` is symmetric.)

- **`[appfn]`** (the interesting case — the β-step):
  `ρ ⊢ ((Close (fn x => t₀ˡ⁰) in ρ₁)ˡ¹ v₂ˡ²)ˡ → (Bind ρ₁[x ↦ v₂] in t₀ˡ⁰)ˡ`.
  From `(Ĉ, ρ̂) ⊧ ie` we have `(Ĉ, ρ̂) ⊧ (Close (fn x => t₀ˡ⁰) in ρ₁)ˡ¹`, which by `[close]`
  gives `{fn x => t₀ˡ⁰} ⊆ Ĉ(l₁)` and `ρ₁ R ρ̂`. We also have `(Ĉ, ρ̂) ⊧ v₂ˡ²`
  (if `v₂ = c`, immediate; if `v₂ = Close t₂ in ρ₂`, it follows from `(Ĉ, ρ̂) ⊧ v₂ˡ²`).
  Now the **universally quantified formula** of the `[app]` clause — which *simulates every
  possible call* `∀(fn x => t₀ˡ⁰) ∈ Ĉ(l₁): Ĉ(l₂) ⊆ ρ̂(x) ∧ (Ĉ,ρ̂) ⊧ t₀ˡ⁰ ∧ Ĉ(l₀) ⊆ Ĉ(l)` —
  applies to the abstraction we just found in `Ĉ(l₁)`. It gives `(Ĉ, ρ̂) ⊧ t₀ˡ⁰`,
  `Ĉ(l₀) ⊆ Ĉ(l)`, and `ρ₁[x ↦ v₂] R ρ̂` (because `Ĉ(l₂) ⊆ ρ̂(x)` covers the new binding).
  These are exactly the premises of `[bind]`, so `(Ĉ, ρ̂) ⊧ ie′`. ✔

- **`[bind2]`** (returning from a call): `ρ ⊢ (Bind ρ₁ in v₁ˡ¹)ˡ → v₁ˡ`.
  From `(Ĉ, ρ̂) ⊧ ie` we have `(Ĉ, ρ̂) ⊧ v₁ˡ¹` and `Ĉ(l₁) ⊆ Ĉ(l)`. Conclude by the
  **Fact** below. ✔

  > **Fact `[slide 98]`.** If `(Ĉ, ρ̂) ⊧ itˡ¹` and `Ĉ(l₁) ⊆ Ĉ(l₂)` then `(Ĉ, ρ̂) ⊧ itˡ²`.
  > *(Acceptability is preserved when the value flows into a **larger** cache entry — this
  > is the "flow" in control-**flow** analysis.)*
∎

**Corollary (worked on slide 99).** For `e ≜ ((fn x => x¹)² (fn y => y³)⁴)⁵` with
`e →* (Close (fn y => y³) in [])⁵`: since `(Ĉ, ρ̂) ⊧ e`, subject reduction gives
`(Ĉ, ρ̂) ⊧ (Close (fn y => y³) in [])⁵` — the resulting closure is acceptable, i.e.
**predicted**.

---

## 2. Existence of a least analysis — `CFA-for-FUN`

### CFA.P2 The set of acceptable analyses is a **Moore family**  `[CFA-FUN / slide 104–108]` ★★★
**Def.** A **Moore family** (model-intersection property) is a subset `Y` of a complete
lattice `L` closed under glbs: `⊓Y′ ∈ Y` for **all** `Y′ ⊆ Y` (including `Y′ = ∅`, whose glb
is `⊤`). A Moore family is therefore never empty and has a least element `⊓Y`.

**The lattice `[slide 104]`.** Order proposed solutions **pointwise**:
`(Ĉ₁, ρ̂₁) ⊑ (Ĉ₂, ρ̂₂)` iff `∀l. Ĉ₁(l) ⊆ Ĉ₂(l)` and `∀x. ρ̂₁(x) ⊆ ρ̂₂(x)`.
Smaller = fewer predicted flows = **more precise**. This makes the solution space a
**complete lattice**.

**Th.** For all `ie ∈ IExp`, the set `{(Ĉ, ρ̂) | (Ĉ, ρ̂) ⊧ ie}` is a Moore family.
**Proof idea (slide 107).** By **coinduction** on `ie`: assume `∀i ∈ I. (Ĉᵢ, ρ̂ᵢ) ⊧ ie` and
show `⊓ᵢ (Ĉᵢ, ρ̂ᵢ) ⊧ ie`, checking that every clause (all of which are **conjunctions of
inclusions** `X ⊆ Ĉ(l)` / `Ĉ(l) ⊆ ρ̂(x)`) survives pointwise intersection. ∎

**Corollaries `[slide 108]`.**
1. **Every expression admits an analysis**: take `Y′ = ∅`; then `⊓∅ = ⊤` is acceptable.
   (The totally imprecise `(Ĉ⊤, ρ̂⊤)` always works.)
2. **Every expression has a *least* analysis**: take `Y′` = the whole set of acceptable
   analyses; `⊓Y′` is acceptable and is below every other one — hence **the most precise**.

### CFA.P3 Acceptability must be **coinductive**: the inductive variant is not a Moore family  `[CFA-FUN / slide 110–111]` ★★
**Prop.** If acceptability were defined **inductively** (relation `⊧′` = *least* fixpoint),
there exists `e*` such that `{(Ĉ, ρ̂) | (Ĉ, ρ̂) ⊧′ e*}` is **not** a Moore family.
**Proof idea.** Take a program with a **circular dependency** (a self-application, e.g.
`fn x => (x x)`). With the **greatest** fixed point everything is fine — the circular
constraint is satisfied by any consistent over-approximation. With the **least** fixed point
the circularity can never be discharged, and the analysis collapses to the empty solution
`∅`, which is not closed under intersection with the acceptable ones. ∎
*Moral: **inductive definitions are too strict** — they exclude valid over-approximations.
Acceptability is a **check**, not a derivation.*

---

## 3. The syntax-directed specification `⊧s` — `CFA-for-FUN`

### CFA.P4 The syntax-directed solution is **unique**  `[CFA-FUN / slide 125–126]` ★★
**Th.** If `⊧′s` and `⊧″s` both satisfy the syntax-directed clauses, then
`(Ĉ, ρ̂) ⊧′s e ⟺ (Ĉ, ρ̂) ⊧″s e` for all `e`.
**Proof.** By **structural induction** on `e`.
- `cˡ`: trivial (both clauses are `true`).
- `xˡ`: both read `ρ̂(x) ⊆ Ĉ(l)` — identical, hence equivalent.
- `(fn x => t₀ˡ⁰)ˡ`: both read `{fn x => e₀} ⊆ Ĉ(l) ∧ (Ĉ,ρ̂) ⊧s e₀`; the first conjunct is
  identical, the second is equivalent by the induction hypothesis on `t₀ˡ⁰`.
- the remaining cases (`[fun]`, `[app]`, `[if]`, `[let]`, `[op]`) are analogous: in each,
  both relations satisfy the **same defining clause**, so their equivalence reduces to the
  equivalence of the premises, which is the IH. ∎
**Consequence `[slide 125]`.** Because the definition is syntax-directed (fully determined by
the structure of the expression), **inductive and coinductive readings coincide** — there is
no choice to minimize over, so speaking of "the least relation" here would be misleading.

### CFA.P5 …whereas the **non**-syntax-directed `⊧` is *not* unique  `[CFA-FUN / slide 127]` ★★
**Claim.** For `⊧′, ⊧″` satisfying the original (non-SD) clauses, one **cannot** establish
`(Ĉ,ρ̂) ⊧′ e ⟺ (Ĉ,ρ̂) ⊧″ e`.
**Proof (counterexample).** Take `a ≜ ((fn x => a⁴)¹ 0²)³` (a self-referential application)
with `(fn x => a⁴) ∈ Ĉ(1)` and `Ĉ(2) = Ĉ(3) = ρ̂(x) = ∅`. The `[app]` clause creates a
**circular** requirement on `a⁴` itself: the greatest solution accepts it, the least rejects
it. Hence two different relations both satisfy the clauses. ∎ (This is why CFA.P2 needs
coinduction and CFA.P4 does not.)

### CFA.P6 Preservation of solutions: `⊧s` ⟹ `⊧`  `[CFA-FUN / slide 128–132]` ★★★
**Setup `[slide 128–129]`.** Restrict to the finite universe of the program `e*`:
`Lab*`, `Var*`, `Term*` (labels/variables/subterms **occurring in `e*`**), and define the
greatest solution within those bounds
`Ĉ⊤(l) = Term*` if `l ∈ Lab*` (else `∅`), `ρ̂⊤(x) = Term*` if `x ∈ Var*` (else `∅`).

**Prop.** If `(Ĉ, ρ̂) ⊧s e*` and `(Ĉ, ρ̂) ⊑ (Ĉ⊤, ρ̂⊤)` (the **boundedness condition**), then
`(Ĉ, ρ̂) ⊧ e*`.
**Proof sketch `[slide 132]`.**
1. Restrict to `Exp*`, the sub-expressions of `e*`.
2. By **syntax-directedness**, `(Ĉ,ρ̂) ⊧s e*` ⟹ `∀e ∈ Exp*. (Ĉ,ρ̂) ⊧s e` (all subterms have
   *already* been checked, up front).
3. By **coinduction**, show each syntax-directed clause implies the original one:
   `[con], [var], [if], [let], [op]` are literally identical; `[fn], [fun]` are **stronger**
   in the SD version; `[app]` — `⊧s` already enforces everything `⊧` demands at the call site,
   because the function bodies were analysed in step (2). ∎
**Slogan `[slide 130]`.** `⊧` *checks when needed* (during the simulated evaluation);
`⊧s` *checks in advance* (all subterms upfront) — so nothing is missing at call time.

### CFA.P7 The converse **fails**  `[CFA-FUN / slide 133]` ★★★
**Claim.** `(Ĉ,ρ̂) ⊧ e*` does **not** imply `(Ĉ,ρ̂) ⊧s e*`.
**Proof (counterexample).** `loop ≜ let f = fn x => (x x) in 0`. The function `f` is **never
applied**, and the program evaluates to `0`. The original `⊧` **never checks** the body
`(x x)` (unreachable code is only checked when a call is simulated), so a very precise
`(Ĉ,ρ̂)` is acceptable. But `⊧s` **does** analyse every body, and forces constraints on
`(x x)`. Hence `⊧s ⊊ ⊧`: the syntax-directed analysis is **strictly more restrictive**
(sound, but less precise on dead code). ∎

### CFA.P8 Existence of a least syntax-directed solution  `[CFA-FUN / slide 134–135]` ★★★
**Th.** `{(Ĉ, ρ̂) ∈ (Cache* × Env*) | (Ĉ,ρ̂) ⊧s e}` is a **Moore family**.
**Proof `[slide 135]`.** `(Ĉ⊤*, ρ̂⊤*)` is the greatest element of the (now **finite**) lattice
`Cache* × Env*`. By structural induction on the sub-expressions `e` of `e*` show:
 (a) `(Ĉ⊤*, ρ̂⊤*) ⊧s e`;
 (b) `(Ĉ₁,ρ̂₁) ⊧s e` and `(Ĉ₂,ρ̂₂) ⊧s e` ⟹ `((Ĉ₁,ρ̂₁) ⊓ (Ĉ₂,ρ̂₂)) ⊧s e`.
Both then hold for `e = e*`. Now take any `Y ⊆ {(Ĉ,ρ̂) | (Ĉ,ρ̂) ⊧s e}`. Since
`Cache* × Env*` is **finite**, `Y = {(Ĉᵢ, ρ̂ᵢ) | i ∈ {1..n}}` for some `n ≥ 0`, and
`⊓Y = (Ĉ⊤*, ρ̂⊤*) ⊓ (Ĉ₁,ρ̂₁) ⊓ … ⊓ (Ĉₙ,ρ̂ₙ)` is acceptable by (a) (the `n = 0` case) and
(b) (iterated). ∎
**Corollaries.** Every `e*` admits a CFA below `(Ĉ⊤, ρ̂⊤)`, and a **least** one — so all the
properties of the original analysis carry over to the syntax-directed one.
*Note the proof is by **structural induction** here (not coinduction), precisely because `⊧s`
is syntax-directed and the universe is finite.*

---

## 4. Constraint-based 0-CFA and the solving algorithm — `CFA-for-FUN`

### CFA.P9 Preservation of solutions: constraints ⟺ `⊧s`  `[CFA-FUN / slide 166–167]` ★★
**Prop.** If `(Ĉ, ρ̂) ⊑ (Ĉ⊤, ρ̂⊤)` then `(Ĉ, ρ̂) ⊧c C*⟦e*⟧ ⟺ (Ĉ, ρ̂) ⊧s e*`.
**Proof sketch.** A simple **structural induction** on `e` shows the equivalence for all
sub-terms of `e*`. In the function-application case `(t₁ˡ¹ t₂ˡ²)ˡ`, the boundedness assumption
`(Ĉ,ρ̂) ⊑ (Ĉ⊤, ρ̂⊤)` is what guarantees `Ĉ(l₁) ⊆ Term*`, so that the finite family of
**conditional constraints** `{t} ⊆ Ĉ(l₁) ⟹ …` (one per subterm `t`) captures exactly the
universally quantified premise of the `[app]` clause. ∎
**Consequence.** Computing the **least solution of the constraints** gives exactly the
**least `⊧s`-solution**, hence (by CFA.P6) a valid CFA of `e*`.

### CFA.P10 Correctness of the worklist algorithm  `[CFA-FUN / slide 201–203]` ★★★
**Prop.** On input `C*⟦e*⟧`, the algorithm **terminates** and its result `(Ĉ, ρ̂)` satisfies
`(Ĉ, ρ̂) = ⊓ {(Ĉ′, ρ̂′) | (Ĉ′, ρ̂′) ⊧c C*⟦e*⟧}` — it is the **least solution**.
**Proof sketch `[slide 202–203]`.**
- **Termination.** Steps 1, 2, 4 obviously terminate; step 3 (propagation) works over the
  **finite** set `Term*` and performs only **monotone updates** (data fields `D[·]` only
  grow), so it stabilizes.
- **Soundness / minimality.** For any solution `(Ĉ′, ρ̂′) ⊧c C*⟦e*⟧` the algorithm maintains
  the **invariant** `D[C(l)] ⊆ Ĉ′(l)` and `D[r(x)] ⊆ ρ̂′(x)`, hence at the end
  `(Ĉ, ρ̂) ⊑ (Ĉ′, ρ̂′)`: the computed result is contained in **every** solution.
- **It *is* a solution.** Assume, for contradiction, that some constraint `cc ∈ C*⟦e*⟧` is
  violated by `(Ĉ, ρ̂)`. Then the propagation step would still have work to do on `cc` and
  the algorithm would not have terminated — contradiction. So `(Ĉ, ρ̂) ⊧c C*⟦e*⟧`.
Being a solution *and* below every solution, it is the glb. ∎
**Corollary `[slide 201]`.** The computed `(Ĉ, ρ̂)` satisfies `(Ĉ, ρ̂) ⊧ e*`
(via CFA.P9 + CFA.P6): **solving the constraints yields a sound analysis**.

### CFA.P11 Complexity of 0-CFA  `[CFA-FUN / slide 163, 200]` ★★
**Th.** Let `n = |e*|`. Naively `O(n²)` constraints and `O(n⁴)` conditional constraints;
**refined**, every construct **except application** contributes a single constraint, and each
application `O(n)` conditional ones — so `O(n)` constraints and `O(n²)` conditional
constraints. Worklist solving is then **cubic, `O(n³)`**, in the worst case.
**Proof (counting).** Each of the `O(n)` subterms generates `O(1)` plain and `O(n)`
conditional constraints; each of the `O(n)` cache/env cells can grow at most `O(n)` times
(it holds a subset of `Term*`, `|Term*| = O(n)`), and each growth triggers `O(n)` propagation
steps. ∎ *Punchline: **polynomial despite higher-order functions**.*

### CFA.P12 Complexity of uniform k-CFA is **exponential**  `[CFA-FUN / slide 259–262]` ★★
**Th.** Even for `k = 1`, uniform k-CFA has exponential worst-case complexity.
**Proof (counting, slide 260).** Let `n` = program size, `p` = number of variables.
Contexts `Δ` have `O(n)` elements, so there are `O(n·p)` pairs `(x, δ)` and `O(n·n)` pairs
`(l, δ)` — the abstract state `(Ĉ, ρ̂)` is an `O(n²)`-tuple of values from `Val̂`.
But `Val̂ = ℘(Term × Cenv)`, and a **context environment** `ce` maps *each* of the `p`
variables to a context: `O(nᵖ)` environments, hence `O(n · nᵖ)` closure pairs and lattice
height `O(n · nᵖ)`. Since `p = O(n)`, this is **exponential**. ∎
**Example `[slide 261]`.** `Var = {x,y}`, `|Δ| = 3` ⟹ `3² = 9` context environments; with 4
functions, 36 abstract closures. With `p` variables, `ce` is a `p`-tuple ⟹ `nᵖ`.
**Contrast (`k = 0`, slide 262).** `Δ` is a singleton, so `Val̂` has height `O(n)` and the
state is an `O(p + n)`-tuple: back to the **polynomial** bound of CFA.P11.
*Fix (slide 263): abstract `Val̂` itself with standard AI techniques to reduce lattice height.*

### CFA.P13 CFA + DFA: soundness and staging  `[CFA-FUN / slide 230–231]` ★
**Th.** The combined CFA+DFA (abstract values in a complete lattice `L`) is **sound** w.r.t.
the operational semantics — *the same proof techniques as CFA.P1 apply* — and the algorithm
**terminates** provided `L` satisfies the **ACC** (as in monotone frameworks).
**Th. (staging).** If the `[if]` clause is modified so that the data-flow component cannot
influence the control-flow component (relation `⊧′D`), then `(Ĉ,D̂,ρ̂,δ̂) ⊧′D e` guarantees
`(Ĉ,ρ̂) ⊧ e`, so one may solve **control flow first, data flow afterwards**, still obtaining
the least solution of the combined constraint set. ∎

### CFA.P14 Checking vs computing (library specifications)  `[CFA-FUN / slide 204]` ★
**Guarantee.** If `(Ĉ,ρ̂) ⊧ e*` is used as a **specification** of a library `e*`, then any
other library `e′*` with `(Ĉ,ρ̂) ⊧ e′*` can safely replace `e*` — all properties the client
derived from `(Ĉ,ρ̂)` still hold. *(Acceptability is a **check**, and checks compose.)*

---

## 5. CFA for the π-calculus — `CFA-for-Pi`

Analysis result `(ρ, κ)`: `ρ(x)` = the (canonical) names variable `x` may be bound to,
`κ(n)` = the names (tuples) that may be **communicated over** channel `n`.

### PI.P1 Disciplined α-renaming / canonical names  `[CFA-Pi / slide 45]` ★★
Because of α-conversion, name identity is not preserved by reduction. Fix: work with
**equivalence classes** `⌊n⌋` (the *canonical name*), with `⌊x⌋ = x`, and allow substitution
only **within** an equivalence class. All the results below are stated on `⌊P⌋`.

### PI.P2 Congruence lemma, substitution lemma, subject reduction  `[CFA-Pi / slide 43, 46]` ★★★
**Lemma (congruence).** If `P ≡ Q` then `(ρ, κ) ⊧P ⌊P⌋ ⟺ (ρ, κ) ⊧P ⌊Q⌋`.
**Substitution lemma.** If `(ρ, κ) ⊧P ⌊P⌋` and `⌊m⌋ ⊆ ρ(x)`, then `(ρ, κ) ⊧P ⌊P[m/x]⌋`.
**Th. (subject reduction).** If `(ρ, κ) ⊧P ⌊P⌋` and `P → Q`, then `(ρ, κ) ⊧P ⌊Q⌋`.
**Proof structure.** Induction on the reduction; the communication rule
`n̄⟨m⟩.P | n(x).Q → P | Q[m/x]` is discharged by the substitution lemma, whose hypothesis
`⌊m⌋ ⊆ ρ(x)` is exactly what the `[in]`/`[out]` clauses guarantee (`κ(n) ⊆ ρ(x)` and
`⌊m⌋ ⊆ κ(n)`); the structural-congruence steps by the congruence lemma. ∎
*Same shape as CFA.P1: **the analysis estimate is invariant under evaluation**.*

### PI.P3 Existence of a least analysis  `[CFA-Pi / slide 47]` ★★
**Th.** The set of acceptable `(ρ, κ)` for a process `P*` is a **Moore family**, hence a least
(most precise) analysis exists. **Proof.** As CFA.P2: all clauses are conjunctions of
inclusions, which are preserved by pointwise intersection. ∎

### PI.P4 Imprecision of 0-CFA on π  `[CFA-Pi / slide 44]` ★★
**Claim.** The analysis is **context-insensitive**: for
`P₁ ≜ a(x) | ā⟨b⟩`, `P₂ ≜ a(x) + ā⟨b⟩`, `P₃ ≜ a(x) . ā⟨b⟩` the estimate gives `ρ(x) ⊇ {b}`
in **all three** cases, although the communication can actually happen only in `P₁`
(in `P₂` the choice discards one branch; in `P₃` the output is sequenced *after* the input).
∎ *(Over-approximation: the price of a sound, cheap analysis.)*

### PI.P5 Adequacy for well-behaved processes  `[CFA-Pi / slide 63–64]` ★★
**Def.** `P*` is **dynamically well-behaved** if whenever it evolves into (a process
structurally congruent to) `C[(n⟨m⃗⟩.R + R′) | (n(x⃗).Q + Q′)]`, then `|m⃗| = |x⃗|` (matching
arities). `P*` is **statically well-behaved** if there exist `ρ, κ` with `(ρ,κ) ⊧P P* : ∅`
(the **error component `ψ` is empty**).
**Th. (adequacy).** Statically well-behaved ⟹ dynamically well-behaved.
**Proof.** By PI.P2 (subject reduction), the estimate `(ρ,κ)` with `ψ = ∅` remains valid along
every reduction; the clauses put a mismatching arity **into `ψ`**, so an empty `ψ` means no
reachable communication can mismatch. ∎ *(The analysis **guarantees no runtime arity
mismatch** can occur.)*

### PI.P6 Adequacy for well-sorted processes  `[CFA-Pi / slide 65–69]` ★★
**Def.** A **sorting** `Σ : Sort → Sort*` assigns to each sort the sequence of sorts of the
names that may be communicated over it (sorts are preserved by disciplined α-renaming).
`P*` is **statically well-sorted** if `(ρ,κ) ⊧P P* : ∅` and, for every constant `n`,
`σ(κ(n)) ⊆ {Σ(σ(n))}` — *everything the CFA predicts for channel `n` has the shape prescribed
by `Σ`*.
**Th. (adequacy).** Statically well-sorted ⟹ dynamically well-sorted (no runtime arity **or**
sort mismatch). **Proof.** As PI.P5, using subject reduction plus the componentwise extension
of `σ` to tuples/sets. ∎ *(This is a **type system obtained for free** from the CFA — the
"CFA vs type systems" punchline of slide 86.)*

### PI.P7 Security properties: secrecy, non-leaking, taint safety  `[CFA-Pi / slide 70–84]` ★★
Same **pattern** (slide 85) instantiated three times: define a *dynamic* property, define a
*static* one as a side condition on `(ρ, κ)`, prove **static ⟹ dynamic** by subject reduction.
- **Secrecy-preserving**: assign security levels to channels; require that whatever `κ(n)`
  predicts for a public channel contains no secret name. Static ⟹ dynamically no secret is
  ever sent on a public channel.
- **Non-leaking**: classify names; require the estimate never lets a confidential name reach
  a low channel.
- **Taint safety**: classify names as tainted/untainted; require `κ` to predict no tainted
  value flowing into a sensitive sink. Static taint-safety ⟹ dynamic taint-safety.
**Conclusion (slide 87–88).** *Control Flow Analysis computes a sound approximation of the
communications, and every one of these safety properties is a **decidable side condition on
the least estimate**.*

---

## Recurring proof patterns

1. **Subject reduction** (CFA.P1, PI.P2) is *the* correctness argument of CFA: induction on
   the evaluation/reduction tree, showing the estimate stays acceptable. The `[appfn]` /
   communication case is always the crux, and it is discharged by the universally quantified
   premise of the application/input clause (which *simulates every possible call*).
2. **Existence of a least analysis** = the acceptability clauses are conjunctions of
   **inclusions**, hence closed under pointwise intersection ⟹ **Moore family** ⟹ least
   element (CFA.P2, CFA.P8, PI.P3). `⊓∅ = ⊤` gives existence for free.
3. **Coinduction vs induction**: coinduction for the non-syntax-directed `⊧` (circular
   dependencies, CFA.P3, CFA.P5); structural induction for the syntax-directed `⊧s` and the
   constraints (uniqueness CFA.P4, finiteness CFA.P8).
4. **"⟹ but not ⟸"** (CFA.P7): the syntax-directed/constraint versions are *sound but
   stricter*, and dead code is the counterexample that separates them.
5. **Complexity = count constraints × lattice height** (CFA.P11, CFA.P12): 0-CFA cubic;
   context environments are what blow k-CFA up to exponential.
6. **Static ⟹ dynamic adequacy** (PI.P5–P7): every π-calculus safety property is proved by
   the *same* two ingredients — subject reduction + an emptiness/shape side condition on the
   estimate.
