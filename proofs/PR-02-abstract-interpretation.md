# Proofs — Abstract Interpretation (order theory · Galois connections · domains · fixpoints · LCL)

> Every theorem/lemma/counterexample **proved on the slides** of lectures 11–16.
> Statement first, then the proof as the slides give it. Source `[lec NN / slide M]`.
> Importance: **★★★** core · **★★** secondary · **★** minor / stated-without-proof.
> See [`../overviews/08`–`12`](../overviews/README.md) and
> [`../exercises/EX-02-abstract-interpretation.md`](../exercises/EX-02-abstract-interpretation.md).

Notation: concrete domain `(C, ≤)` (usually `℘(Z)` or `℘(Σ)`, ordered by `⊆`),
abstract domain `(A, ⊑)`, `α : C → A`, `γ : A → C`, `A(·) ≜ γ∘α` (the closure /
"abstraction of"), `F : C → C` concrete operator, `F# : A → A` abstract one,
`Fᴬ ≜ α∘F∘γ` the **best correct approximation** (BCA).

---

## 0. Why static analysis must approximate — lect. 12

### AI.P0 No non-trivial semantic property is decidable  `[lec 12 / slide 5–9]` ★
**Th. (Rice, via halting).** Any non-trivial property of program behaviour is undecidable;
in particular an analyser cannot always answer *yes/no*, so it must be allowed to answer
**"don't know"**.
**Proof (sketch, as on the slides).** Reduce the halting problem: an exact analyser for
"does `c` reach the error?" decides halting. Hence an analyser is either **unsound**
(misses cases), **incomplete** (false alarms), or **non-terminating**. Abstract
interpretation deliberately chooses *sound + incomplete + terminating*. ∎
**Corollary (slide 3, tongue-in-cheek).** "If all programs are likely interesting, none
of them really is."

---

## 1. Abstract operators: soundness, best abstraction, completeness — lect. 12, 14, 15

### AI.P1 The three equivalent formulations of a **sound** abstract operator  `[lec 14 / slide 10–12]` ★★★
**Th.** For `F : C → C` and `F# : A → A`, the following are equivalent:
1. `∀a ∈ A. F(γ(a)) ≤ γ(F#(a))`  (concretize-then-run ≤ run-then-concretize)
2. `∀a ∈ A. α(F(γ(a))) ⊑ F#(a)`
3. `∀c ∈ C. α(F(c)) ⊑ F#(α(c))`

**Proof.** (1) ⟺ (2) is immediately the Galois connection `c ≤ γ(a) ⟺ α(c) ⊑ a`
instantiated at `c := F(γ(a))`.
(3) ⟹ (2): instantiate `c := γ(a)` and use `α(γ(a)) ⊑ a` (reductivity, GC.2) plus
monotonicity of `F#`.
(2) ⟹ (3): for `c ∈ C`, `c ≤ γ(α(c))` (extensivity, GC.1), so by monotonicity
`α(F(c)) ⊑ α(F(γ(α(c)))) ⊑ F#(α(c))`. ∎

### AI.P2 The BCA is the ⊑-least sound abstraction  `[lec 14 / slide 17]` ★★★
**Th.** `Fᴬ ≜ α ∘ F ∘ γ` is sound, and `F#` sound ⟹ `Fᴬ ⊑ F#` (pointwise).
**Proof.** Soundness: formulation (2) of AI.P1 holds with equality by definition.
Minimality: soundness of `F#` in form (2) reads `α(F(γ(a))) ⊑ F#(a)`, i.e.
`Fᴬ(a) ⊑ F#(a)` for every `a`. ∎ *(So "best" = most precise sound choice; it exists
whenever `α` exists, i.e. whenever the domain is closed under meet — slide 77 of lec 13.)*

### AI.P3 Sound operators compose  `[lec 14 / slide 19]` ★★
**Th.** If `F#₁` and `F#₂` are sound abstractions of the monotone `F₁, F₂ : C → C`, then
`F#₂ ∘ F#₁` is a sound abstraction of `F₂ ∘ F₁`.
**Proof.** Chain the two soundness inequalities (form (1)), using monotonicity of `F₂`:
```
(F₂ ∘ F₁)(γ(a)) = F₂(F₁(γ(a))) ⊆ F₂(γ(F#₁(a)))        [F₁ sound, F₂ monotone]
                              ⊆ γ(F#₂(F#₁(a)))          [F₂ sound]
                              = γ((F#₂ ∘ F#₁)(a))
```
∎

### AI.P4 …but the composition of BCAs need **not** be the BCA of the composition  `[lec 14 / slide 20]` ★★
**Remark.** `Fᴬ₂ ∘ Fᴬ₁ = α∘F₂∘γ∘α∘F₁∘γ` versus `(F₂∘F₁)ᴬ = α∘(F₂∘F₁)∘γ`.
**Proof (of the inequality).** The composition performs an **extra round trip `γ∘α`** in
the middle. Since `γ∘α` is extensive (GC.1), that round trip can only lose precision:
`(F₂ ∘ F₁)ᴬ ⊑ Fᴬ₂ ∘ Fᴬ₁`, and the inclusion can be strict. ∎ *(Hence in general
`(F₂ ∘ F₁)ᴬ ≠ Fᴬ₂ ∘ Fᴬ₁` — precision is not compositional; this is the seed of the
completeness question.)*

### AI.P5 Correctness vs completeness of the Sign operators  `[lec 12 / slide 45–49] [lec 15 / slide 49–53]` ★★★
**Def.** `F#` is **correct/sound** on `A` iff `F# ⊒ α∘F∘γ`; it is **complete** iff
`F# ∘ α = α ∘ F` (it returns the *best* abstraction of the concrete result).
- `×#` is **complete** on `Sign`: `∀n,m. α(n) ×# α(m) = α(n × m)` — Brahmagupta's rule of
  signs is exact, because the sign of a product is a function of the signs of the factors.
- `+#` is only **correct** on `Sign`: `∀n,m. α(n) +# α(m) ⊒ α(n + m)`, and the inclusion is
  strict (e.g. `α(1) +# α(−1) = Z>0 +# Z<0 = ⊤` but `α(1 + (−1)) = Z=0`).
- On `Int` (intervals) both `+#` and `×#` are **complete**:
  `[n,m] + [p,r] = [n+p, m+r]` and `[n,m] × [p,r] = [n×p, m×r]` (with care about signs).

### AI.P6 Completeness forces the operator to be the BCA  `[lec 15 / slide 51]` ★★
**Th.** If `F#` is complete (`F# ∘ α = α ∘ F`) then `F# = Fᴬ`.
**Proof.** `Fᴬ = α ∘ F ∘ γ = (α ∘ F) ∘ γ = (F# ∘ α) ∘ γ = F# ∘ (α ∘ γ) = F#`,
using `α∘γ = id` (Galois **insertion**). ∎
**Corollary.** *Completeness is an intrinsic property of the **domain**, not of the chosen
operator*: if the BCA is incomplete, then **every** sound `F#` is incomplete. (Restated in
LCL, lec 16 / slide 17.)

### AI.P7 Absolute value is **not** complete on `Int`  `[lec 15 / slide 53]` ★★
**Claim.** `|[a,b]|# ≜ [a,b]` if `a ≥ 0`; `[−b,−a]` if `b ≤ 0`; `[0, max(−a,b)]` if `a < 0 < b`.
**Proof (counterexample).** Take `S = {−6, −4, 1}`. Concretely `|S| = {1,4,6}` and
`α(|S|) = [1,6]`. Abstractly `α(S) = [−6,1]` and `|[−6,1]|# = [0,6] ≠ [1,6]`.
So `α ∘ | · | ≠ | · |# ∘ α`: the abstract result is strictly less precise. ∎
*(Contrast: on `S′ = {−6,−4,−1}` we get `|[−6,−1]|# = [1,6] = α(|S′|)` — completeness can
hold **locally** and fail globally. This is precisely the observation LCL exploits.)*

---

## 2. Galois connections — the mandatory Ex. 1–12 — lect. 13

Throughout: `(α, γ)` is a **GC** iff `∀c ∈ C, a ∈ A. c ≤ γ(a) ⟺ α(c) ⊑ a`.
A **Galois insertion (GI)** additionally satisfies `α ∘ γ = id`.
*(These twelve are flagged "they are all mandatory!" on the slides — the highest-yield
proofs of the whole AI block. Statements also in [EX-02 §3](../exercises/EX-02-abstract-interpretation.md).)*

### GC.P1 `γ∘α` is **extensive**: `∀c. c ≤ γ(α(c))`  `[lec 13 / slide 90–91]` ★★★
**Proof.** Take `a ≜ α(c)`. Reflexivity gives `α(c) ⊑ a`; by the GC (right-to-left),
`α(c) ⊑ a ⟺ c ≤ γ(a) = γ(α(c))`. ∎
*Meaning: abstracting and coming back **loses information** — you can only grow.*

### GC.P2 `α∘γ` is **reductive**: `∀a. α(γ(a)) ⊑ a`  `[lec 13 / slide 93–94]` ★★★
**Proof.** Take `c ≜ γ(a)`. Reflexivity gives `γ(a) ≤ γ(a)`, i.e. `c ≤ γ(a)`; by the GC
(left-to-right), `α(c) = α(γ(a)) ⊑ a`. ∎
*Meaning: concretizing and coming back **cannot lose** anything (and in a GI it is exact).*

### GC.P3 `α` and `γ` are **monotone**  `[lec 13 / slide 96–97]` ★★★
**Proof.** Let `c ≤ c₁`. By GC.P1, `c ≤ c₁ ≤ γ(α(c₁))`; by the GC, `c ≤ γ(α(c₁))` gives
`α(c) ⊑ α(c₁)`. Dually, let `a ⊑ a₁`. By GC.P2, `α(γ(a)) ⊑ a ⊑ a₁`; by the GC,
`α(γ(a)) ⊑ a₁` gives `γ(a) ≤ γ(a₁)`. ∎

### GC.P4 Equivalent definition of a GC  `[lec 13 / slide 98–99]` ★★★
**Th.** `(α, γ)` monotone with `γ∘α` extensive and `α∘γ` reductive **⟺** `(α, γ)` is a GC.
**Proof.** (⟸) is GC.P1–P3. (⟹):
- if `c ≤ γ(a)`: monotonicity of `α` gives `α(c) ⊑ α(γ(a))`, and reductivity gives
  `α(γ(a)) ⊑ a`, so `α(c) ⊑ a`;
- if `α(c) ⊑ a`: monotonicity of `γ` gives `γ(α(c)) ≤ γ(a)`, and extensivity gives
  `c ≤ γ(α(c))`, so `c ≤ γ(a)`. ∎
*(This is the definition you actually use in exercises: prove the four small facts.)*

### GC.P5 Round-trips: `γ∘α∘γ = γ` and `α∘γ∘α = α`  `[lec 13 / slide 102–103]` ★★
**Proof.** `α(γ(a)) ⊑ a` (GC.P2) + monotonicity of `γ` ⟹ `γ(α(γ(a))) ≤ γ(a)`.
Conversely `γ(a) ≤ γ(α(γ(a)))` is GC.P1 at `c := γ(a)`. Antisymmetry gives `γ∘α∘γ = γ`.
Symmetrically, `c ≤ γ(α(c))` (GC.P1) + monotonicity of `α` ⟹ `α(c) ⊑ α(γ(α(c)))`, and
`α(γ(α(c))) ⊑ α(c)` is GC.P2 at `a := α(c)`. ∎

### GC.P6 `γ∘α` and `α∘γ` are **idempotent**  `[lec 13 / slide 104–105]` ★★
**Proof.** `(γ∘α)∘(γ∘α) = γ∘(α∘γ∘α) = γ∘α` by GC.P5; dually for `α∘γ`. ∎
**Corollary.** `γ∘α` is a **upper closure operator** (monotone + extensive + idempotent) —
this is the "abstract domain as a closure" view used throughout lect. 14 and 16 (`A(·)`).

### GC.P7 / GC.P8 The two maps determine each other  `[lec 13 / slide 106–109]` ★★★
**Th.** In a GC, each adjoint is uniquely determined by the other:
`γ(a) = ⋁{ c ∈ C | α(c) ⊑ a }` and `α(c) = ⊓{ a ∈ A | c ≤ γ(a) }`.
**Proof (for `γ`).** Let `S_a ≜ {c | α(c) ⊑ a}`. Every `c ∈ S_a` satisfies `α(c) ⊑ a ⟺ c ≤ γ(a)`,
so `γ(a)` is an **upper bound** of `S_a`. Moreover `γ(a) ∈ S_a`, because `α(γ(a)) ⊑ a` (GC.P2).
An upper bound belonging to the set is the **least** upper bound. Hence `γ(a) = ⋁S_a`. ∎
(Dually for `α`, using extensivity.) *Consequence: you may **define** a domain by giving only
`γ` (or only `α`) — the adjoint comes for free, provided the required lubs/glbs exist.*

### GC.P9 `α` preserves **lubs**  `[lec 13 / slide 112–113]` ★★★
**Th.** `α(⋁D) = ⊔{ α(c) | c ∈ D }` for every `D ⊆ C` whose lub exists.
**Proof.** (⊒) Each `c ∈ D` has `c ≤ ⋁D`, so by monotonicity `α(c) ⊑ α(⋁D)`; hence
`⊔{α(c)} ⊑ α(⋁D)`.
(⊑) Let `a ≜ ⊔{α(c) | c ∈ D}`. For every `c ∈ D`, `α(c) ⊑ a`, i.e. (GC) `c ≤ γ(a)`. So
`γ(a)` is an upper bound of `D`, whence `⋁D ≤ γ(a)`, i.e. (GC) `α(⋁D) ⊑ a`. ∎
*(This is the "additivity" of `α` — the standard hallmark of a left adjoint.)*

### GC.P10 `γ` preserves **glbs**  `[lec 13 / slide 114–115]` ★★★
**Th.** `γ(⊓B) = ⋀{ γ(a) | a ∈ B }` for every `B ⊆ A` whose glb exists.
**Proof.** Dual of GC.P9: (≤) by monotonicity of `γ`. (≥) let `c ≜ ⋀{γ(a) | a ∈ B}`; then
`c ≤ γ(a)` for all `a ∈ B`, i.e. `α(c) ⊑ a` for all `a`, so `α(c) ⊑ ⊓B`, i.e. `c ≤ γ(⊓B)`. ∎
*(Consequence: the image `γ(A)` is a **Moore family** — closed under glbs. Same structure
as the CFA existence theorem, [PR-03 CFA.P2](PR-03-control-flow-analysis.md).)*

### GC.P11 GI ⟺ `α` surjective  `[lec 13 / slide 118–119]` ★★★
**Th.** `α∘γ = id` **iff** `α` is surjective.
**Proof.** (⟹) For any `a ∈ A`, `a = α(γ(a))`, so `a` is in the image of `α`.
(⟸) Let `a ∈ A`; by surjectivity `a = α(c)` for some `c`. Then by GC.P5,
`α(γ(a)) = α(γ(α(c))) = α(c) = a`. ∎

### GC.P12 GI ⟺ `γ` injective  `[lec 13 / slide 120–121]` ★★★
**Th.** `α∘γ = id` **iff** `γ` is injective.
**Proof.** (⟹) If `γ(a₁) = γ(a₂)` then `a₁ = α(γ(a₁)) = α(γ(a₂)) = a₂`.
(⟸) By GC.P5, `γ(α(γ(a))) = γ(a)`; injectivity of `γ` gives `α(γ(a)) = a`. ∎
*Reading of GI: no **redundant** abstract elements — distinct abstract values denote
distinct concrete sets. Failure of GI is repaired by **reduction** (quotienting the
redundant elements), lec 15 / slide 32–34 (reduced product).*

---

## 3. Fixpoints and the analysis — lect. 15

### FIX.P1 Fixpoint transfer (soundness of the analysis)  `[lec 15 / slide 54]` ★★★
**Th.** If `F` is monotone and `F#` is a **sound** abstraction of `F`, then
`α(lfp F) ⊑ lfp F#`, i.e. `lfp F ≤ γ(lfp F#)`: **the abstract fixpoint over-approximates the
concrete one**.
**Proof (the slides' diagram, spelled out).** By Kleene, `lfp F = ⋁ₙ Fⁿ(⊥)` and
`lfp F# = ⊔ₙ (F#)ⁿ(⊥#)`. Show `α(Fⁿ(⊥)) ⊑ (F#)ⁿ(⊥#)` by induction on `n`:
- `n = 0`: `α(⊥) ⊑ ⊥#` (holds since `α` is strict / by definition of `⊥#`);
- `n+1`: `α(F(Fⁿ(⊥))) ⊑ F#(α(Fⁿ(⊥)))` (soundness, form (3) of AI.P1)
  `⊑ F#((F#)ⁿ(⊥#))` (IH + monotonicity of `F#`) `= (F#)ⁿ⁺¹(⊥#)`.
Taking lubs and using GC.P9 (`α` preserves lubs) gives `α(lfp F) ⊑ lfp F#`. ∎
*This one theorem is what makes the whole abstract-interpretation edifice sound: you may
compute in `A` and the result still describes all concrete runs.*

### FIX.P2 Fixpoint transfer under **completeness**  `[lec 15 / slide 55]` ★★★
**Th.** If `F` is monotone and `F#` is **complete** (`F# ∘ α = α ∘ F`), then
`α(lfp F) = lfp F#` — the analysis is **exact** on the fixpoint.
**Proof.** Same induction as FIX.P1 but with equalities: `α(Fⁿ(⊥)) = (F#)ⁿ(⊥#)` for all `n`,
then take lubs (GC.P9). ∎
*Together with AI.P6: completeness of the atomic operators ⟹ no loss of precision anywhere,
because completeness is preserved by `;`, `∪` and `fix` (lec 16 / slide 17).*

### FIX.P3 Termination: ACC and widening  `[lec 14 / slide 61–66]` ★★
**Fact.** If `A` satisfies the **ascending chain condition** (no infinite strictly increasing
chain — e.g. `Sign`, the constant domain, bounded-set domains), the Kleene iteration of `F#`
**terminates**. Domains like `Int` or the polyhedra **do not** satisfy the ACC
(`[0,0] ⊏ [0,1] ⊏ [0,2] ⊏ …`).
**Widening.** `∇ : A × A → A` is a widening iff (i) it **over-approximates the join**
(`a₁ ⊔ a₂ ⊑ a₁ ∇ a₂`) and (ii) it **enforces convergence** (every chain `x₀, xₙ₊₁ = xₙ ∇ yₙ`
stabilizes in finitely many steps).
**Th.** The widened iteration `x₀ = ⊥`, `xₙ₊₁ = xₙ ∇ F#(xₙ)` terminates and its limit is a
**post-fixpoint** of `F#`, hence a **sound over-approximation** of `lfp F#` (and of `lfp F`
by FIX.P1). *(Proof: (ii) gives termination; the limit `x` satisfies `F#(x) ⊑ x ∇ F#(x) = x`
by (i); by Tarski, `lfp F# ⊑ x`.)* Narrowing then recovers precision by descending.

---

## 4. Local Completeness Logic — lect. 16

LCL triples `⊢A [P] c [Q]` are valid iff **`Q ⊆ ⟦c⟧P ⊆ A(Q)`**: an IL-style
under-approximating post `Q`, whose abstraction `A(Q)` over-approximates the real behaviour.
Local-completeness proof obligation: `Cᴬ_P(e) ≜ A(⟦e⟧P) = A(⟦e⟧A(P))`.

### LCL.P1 Incompleteness is intrinsic to the domain  `[lec 16 / slide 17]` ★★
**Th.** Completeness is preserved by `;`, `∪` and `fix`; it can only be broken by **atomic**
commands. Moreover, if the **BCA** `⟦e⟧ᴬ` is incomplete then **every** sound `⟦e⟧#` is
incomplete. **Proof.** The second half is AI.P6 (a complete operator must equal the BCA). ∎
*Consequence: assignments are settled for most domains; **guards** are the troublesome ones.*

### LCL.P2 Necessary condition for complete guards  `[lec 16 / slide 18]` ★★
**Lemma.** If a test `b` is complete in `A`, then **both `b` and `¬b` are expressible** in `A`
(i.e. are fixpoints of `A(·)`).
**Proof.** Assume `b` is not expressible. Take `P ≜ b`. Then `A(⟦b?⟧P) = A(b) ≠ b` while the
completeness equation would force the analysis to recover exactly `b` — and symmetrically,
taking `P ≜ ¬b`, one shows `¬b` is not complete. ∎ (Slide: *"assume `b` not expressible, take
`P = b` and show `¬b` is not complete"*.)

### LCL.P3 Necessary **and sufficient** condition for complete guards  `[lec 16 / slide 20–23]` ★★★
**Th.** Let `b` and `¬b` be expressible in `A`. Then `b?` is complete in `A` **iff the join of
any two abstract points below `b` and below `¬b` is expressible** (`a₁ ⊑ b`, `a₂ ⊑ ¬b` ⟹
`a₁ ⊔ a₂ ∈ A`).
**Examples (the slides' checks).**
- `Int`: `(x = 0)` is **not** complete (`x ≠ 0` is not an interval).
- `Int`: `(x > 5)` — both `[6,+∞]` and `[−∞,5]` are expressible, but the join
  `{0,1,10,11}` of two points below them is **not** an interval ⟹ **not** complete.
- `Sign`: `(x > 5)` **not** complete (`x > 5` itself not expressible).
- `Sign⁺` (with `≠0, ≤0, ≥0`): `(x > 0)` **is** complete — every needed join (e.g. `≠0`)
  is in the domain.

### LCL.P4 Convexity lemma  `[lec 16 / slide 35]` ★★★
**Lemma.** If `Cᴬ_P(e)` holds and `P ⇒ R ⇒ A(P)`, then `Cᴬ_R(e)` holds.
**Proof.** Assume `A(⟦e⟧P) = A(⟦e⟧A(P))`. Since `P ⊆ R ⊆ A(P)`, monotonicity gives
```
A(⟦e⟧P) ⊆ A(⟦e⟧R) ⊆ A(⟦e⟧A(R)) = A(⟦e⟧A(P)) = A(⟦e⟧P)
```
(the middle equality uses `A(R) = A(P)`, which follows from `P ⊆ R ⊆ A(P)` by idempotency of
`A`, GC.P6). All inclusions are therefore equalities, so `A(⟦e⟧R) = A(⟦e⟧A(R))`. ∎
**Why it matters:** it is exactly what makes the consequence rule `[relax]` sound —
you may move `P` anywhere **between `P′` and `A(P′)`** without destroying local completeness.

### LCL.P5 The consequence rule `[relax]`  `[lec 16 / slide 34–39]` ★★★
**Rule.** `P′ ⇒ P ⇒ A(P′)`, `⊢A [P′] c [Q′]`, `Q ⇒ Q′ ⇒ A(Q)` ⟹ `⊢A [P] c [Q]`.
It is the IL-style (reversed-Hoare) rule — *weaken the pre, shrink the post* — but **not too
much**: both sides must **preserve the abstraction** (`A(P) = A(P′)`, `A(Q) = A(Q′)`),
which is exactly the convexity condition of LCL.P4. Soundness follows from LCL.P4 plus the
IL soundness argument.

### LCL.P6 Logical correctness of LCL  `[lec 16 / slide 46]` ★★★
**Th.** If `⊢A [P] c [Q]` then `Q ⊆ ⟦c⟧P ⊆ A(Q) = ⟦c⟧#A(P)`.
**Proof.** By induction on the derivation (each rule carries its local-completeness proof
obligation, which is precisely what upgrades the IL under-approximation into the
*equality* `A(Q) = ⟦c⟧#A(P)`). ∎
*Read: an LCL triple simultaneously gives an IL-style **true** under-approximation `Q` and an
AI-style **sound** over-approximation `A(Q)` — the two halves of the picture.*

### LCL.P7 The verification theorem (correctness **or** true bug)  `[lec 16 / slide 47]` ★★★
**Th.** If `A(Spec) = Spec` (the specification is expressible), then any provable triple
`⊢A [P] c [Q]` **either** proves the program correct (when `Q ⊆ Spec`) **or** exposes only
**true positives** (when `Q ∖ Spec ≠ ∅`).
**Proof.**
```
⟦c⟧P ⊆ Spec  ⟺  A(⟦c⟧P) ⊆ Spec      [Spec expressible ⇒ A(Spec)=Spec]
             ⟺  A(Q) ⊆ Spec          [LCL.P6]
             ⟺  Q ⊆ Spec             [A extensive, Spec expressible]
```
So `Q ⊄ Spec` implies `⟦c⟧P ⊄ Spec`: the alarm is real (the states in `Q ∖ Spec` are
genuinely reachable, since `Q ⊆ ⟦c⟧P`). ∎
*This is the punchline of the lecture: **one** derivation decides correctness **and**
bug-finding, with no false alarms.*

### LCL.P8 Logical completeness of LCL  `[lec 16 / slide 48]` ★★
**Th.** If `A` is complete for every atomic command occurring in `c`, then every valid triple
`⊢A [P] c [Q]` can be derived.
**Proof.** First derive `⊢A [P] c [⟦c⟧P]` (as in IL.P2, the proof obligations discharge by the
assumed completeness of the atoms); then apply `[relax]` with `Q ⊆ ⟦c⟧P`. ∎

### LCL.P9 Intrinsic logical **in**completeness  `[lec 16 / slide 49–51]` ★★
**Th.** For any Turing-complete language and any non-trivial abstraction `A`, there are valid
triples that cannot be proved. **Proof.** See the full LICS 2021 / JACM version. ∎
*Intuition (slide 51): any non-trivial `A` introduces some imprecision, so a
local-completeness proof obligation `Cᴬ_P(e)` can always be made to fail. HL and IL are
logically complete; **LCL is not** — that is the price of combining both directions.*

### LCL.P10 Mixed HL + LCL rules are **sound**  `[lec 16 / slide 57–58]` ★★
**Th.** `⊢A [P] c [Q] ⟹ {P} c {A(Q)}` and `⊢A [P] c [Q] ⟹ {A(P)} c {A(Q)}`.
**Proof.** By LCL.P6, `⟦c⟧P ⊆ A(Q)` — that *is* the first HL triple. For the second,
`⟦c⟧A(P) ⊆ ⟦c⟧#A(P) = A(Q)` (soundness of `⟦c⟧#` + LCL.P6). ∎

### LCL.P11 `[conj]` is unsound for LCL  `[lec 16 / slide 59–60]` ★★
**Proof (counterexample).** `⊢{⊤} [x=0] x:=1 [x=1]` and `⊢{⊤} [x=1] x:=1 [x=1]` are both
derivable. `[conj]` would give `⊢{⊤} [false] x:=1 [x=1]`, which is invalid
(`⟦x:=1⟧∅ = ∅ ⊉ (x=1)`). ∎ *(Inherited from IL — see [PR-01 IL.P4](PR-01-program-logics.md).)*

### LCL.P12 The nondeterministic-assignment rule is unsound  `[lec 16 / slide 61–62]` ★★
**Claim.** `⊢A [P] x := nondet() [P[v/x]]` (for an arbitrary value `v`) is not sound.
**Proof (counterexample).** In the identity domain: `⊢Id [x=0] x := nondet() [1 = 0] ≡ [false]`.
Not sound, because validity would require `A(Q) ⊇ ⟦c⟧P`, but `Id(false) = ⊥` while
`Id(⟦x:=nondet()⟧(x=0)) = ⊤`. ∎

---

## Recurring proof patterns

1. **Everything about GCs follows from GC.P4**: monotone + extensive `γ∘α` + reductive `α∘γ`.
   Prove those three, then all of GC.P5–P12 are two-line adjunction shuffles.
2. **"Best" arguments** (AI.P2, GC.P7): show the candidate is (a) *in* the set and (b) a
   bound of the set — an upper bound that belongs to the set is the lub.
3. **Precision loss = an extra `γ∘α` round trip** (AI.P4, AI.P7): to refute completeness,
   feed a concrete set whose abstraction "fills in" points the operator then keeps.
4. **Soundness of the analysis = induction on the Kleene chain** (FIX.P1); completeness turns
   every `⊑` in that induction into an `=` (FIX.P2).
5. **Unsoundness of `conj`**: the same `[x=0] / [x=1] ⟹ [false]` counterexample works in
   IL, SIL, ISL and LCL.
