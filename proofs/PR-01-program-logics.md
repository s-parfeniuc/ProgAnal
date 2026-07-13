# Proofs — Program Logics (HL · IL · NC · SIL · SL · ISL · SepSIL)

> Every theorem/lemma/counterexample **proved on the slides** of lectures 03–10,
> collected in one place. Statement first, then the proof exactly as the slides
> give it (reconstructed where the PDF text layer is mangled). Source is noted as
> `[lec NN / slide M]`. Importance tag per the legend in [README.md](README.md):
> **★★★** core · **★★** secondary · **★** minor / stated-without-proof.
>
> Companion files: [`../overviews/`](../overviews/README.md) (full explainers),
> [`../exercises/EX-01-program-logics.md`](../exercises/EX-01-program-logics.md)
> (the same material posed as exercises).

Notation: `⟦c⟧P` forward image · `⟦c⟧ᵒᵖQ` backward pre-image (= `wpp(c,Q)`) ·
`wlp(c,Q) = {σ | ⟦c⟧{σ} ⊆ Q}`.

---

## 1. Hoare Logic — lect. 03–04

### HL.P1 Soundness of HL: every derivable triple is valid  `[lec 03 / slide 28, 31] [lec 04 / slide 29]` ★★★
**Th.** `⊢ {P} c {Q}` ⟹ `⟦c⟧P ⊆ Q`.

**Proof.** By induction on the derivation tree: for each axiom show it is valid;
for each rule assume the premises valid and show the conclusion valid.
- `[skip]`: `⟦skip⟧P = P ⊆ P`. ✔
- `[seq]` (the slide's sample case): from `⟦c₁⟧P ⊆ R` and `⟦c₂⟧R ⊆ Q`,
  `⟦c₁;c₂⟧P = ⟦c₂⟧(⟦c₁⟧P) ⊆ ⟦c₂⟧R ⊆ Q`. ✔ (uses monotonicity of `⟦c₂⟧`)
- the remaining cases are HL.P2–HL.P4. ∎

### HL.P2 Soundness of Floyd's assignment axiom  `[lec 04 / slide 30]` ★★★
**Ax.** `{P} x:=a {∃x′. P[x′/x] ∧ x = a[x′/x]}`.

**Proof.** Take `δ ∈ ⟦x:=a⟧P`. Then `δ = σ[v/x]` for some `σ ⊧ P` with `v = ⟦a⟧σ`.
Let `x′ = σ(x)`. Then `δ(x) = v` and
`⟦a[x′/x]⟧δ = ⟦a[x′/x]⟧σ[v/x] = ⟦a[x′/x]⟧σ = ⟦a⟧σ = v`, so `δ ⊧ (x = a[x′/x])`.
Moreover `⟦P[x′/x]⟧δ = ⟦P[x′/x]⟧σ[v/x] = ⟦P[x′/x]⟧σ = ⟦P⟧σ = true`, so `δ ⊧ P[x′/x]`.
Hence `δ ⊧ ∃x′. P[x′/x] ∧ x = a[x′/x]`. ∎
*(The key step is that `x′` is a fresh ghost naming the **old** value of `x`, so
substituting it back makes both conjuncts insensitive to the update.)*

### HL.P3 Soundness of the conditional rule  `[lec 04 / slide 31]` ★★
**Rule.** `{P∧b} c₁ {Q}`, `{P∧¬b} c₂ {Q}` ⟹ `{P} if b then c₁ else c₂ {Q}`.

**Proof.** Assume `⟦c₁⟧(P∧b) ⊆ Q` and `⟦c₂⟧(P∧¬b) ⊆ Q`. Then, unfolding the
encoding `if b then c₁ else c₂ ≜ b?;c₁ + ¬b?;c₂`:
`⟦if b then c₁ else c₂⟧P = ⟦c₁⟧(⟦b?⟧P) ∪ ⟦c₂⟧(⟦¬b?⟧P) = ⟦c₁⟧(P∧b) ∪ ⟦c₂⟧(P∧¬b) ⊆ Q ∪ Q = Q`. ∎

### HL.P4 Soundness of the while rule (the invariant argument)  `[lec 04 / slide 32]` ★★★
**Rule.** `{P∧b} c {P}` ⟹ `{P} while b do c {P∧¬b}`.

**Proof.** Assume the premise: `⟦c⟧(P∧b) ⊆ P`, i.e. `⟦b?;c⟧P ⊆ P`.
By induction on `k`, `⟦b?;c⟧ᵏP ⊆ P` for every `k ∈ ℕ` (base `k=0` trivial; step
by the premise + monotonicity). Therefore, with `while b do c ≜ (b?;c)⋆; ¬b?`:

```
⟦while b do c⟧P = ⟦¬b?⟧( ⋃_{k=0}^{∞} ⟦b?;c⟧ᵏ P ) ⊆ ⟦¬b?⟧(P) = P ∧ ¬b
```
∎ *(This is exactly why the invariant must be preserved by **every** iteration:
the Kleene star is a union over all `k`.)*

### HL.P5 Incompleteness I — the halting argument  `[lec 04 / slide 33]` ★★★
**Claim.** "Every valid HL triple is derivable" is **false**.

**Proof (counterexample).** `{true} c {false}` is valid **iff** `c` diverges on every
input (`⟦c⟧Σ = ∅ ⊆ ∅`). The set of always-diverging programs is not r.e. (halting
problem), whereas the set of derivable HL triples **is** r.e. (derivations are finite
objects one can enumerate). So the two sets cannot coincide. ∎

### HL.P6 Incompleteness II — the Gödel argument  `[lec 04 / slide 34]` ★★★
**Proof (counterexample).** `{true} skip {Q}` is valid iff `Q` is a tautology of
arithmetic. By Gödel's incompleteness theorem there is no effective proof system whose
theorems are exactly the valid arithmetic assertions; hence no effective HL proof
system can derive exactly the valid triples. ∎
*(Moral: the incompleteness is about **arithmetic**, not about programs — which is
what motivates *relative* completeness.)*

### HL.P7 The `wlp` adjunction  `[lec 04 / slide 36–37]` ★★
**Th.** `⟦c⟧P ⊆ Q ⟺ P ⇒ wlp(c,Q)`, where `wlp(c,Q) ≜ {σ | ⟦c⟧{σ} ⊆ Q}`.

**Proof.** `⟦c⟧P ⊆ Q ⟺ ∀σ∈P. ⟦c⟧{σ} ⊆ Q ⟺ ∀σ∈P. σ ∈ wlp(c,Q) ⟺ P ⊆ wlp(c,Q)`. ∎
So `wlp(c,·)` is the right adjoint of `⟦c⟧`, and `{R} c {Q}` valid `⟺ R ⇒ wlp(c,Q)`:
`wlp(c,Q)` is the **weakest** valid precondition.

### HL.P8 Relative completeness (Cook)  `[lec 04 / slide 35, 38]` ★★★
**Th.** If the assertion language is **expressive** (for every `c` and expressible `Q`,
`wlp(c,Q)` is expressible) and we may consult an **oracle** for implications
`P ⇒ P′`, then every valid HL triple is derivable.

**Proof.** Suppose `{P} c {Q}` is valid, with `P, Q` expressible. By structural
induction on `c` one builds an assertion `R` equivalent to `wlp(c,Q)` such that
`{R} c {Q}` is derivable. Validity gives `⟦c⟧P ⊆ Q`, hence `P ⇒ wlp(c,Q) ≡ R`
(HL.P7). Applying `[cons]` (strengthen the pre) to `{R} c {Q}` yields `{P} c {Q}`. ∎
*Separation of concerns: program reasoning is complete; only arithmetic is not.*

### HL.P9 Which structural rules are valid in HL?  `[lec 03 / slide 45–49]` ★★
Proved as exercises — see [EX-01 HL.2–HL.6](../exercises/EX-01-program-logics.md).
Summary of the verdicts (all by the `⟦c⟧P ⊆ Q` reading):
`{P}c{Q} ⟹ {P∧R}c{Q∧R}` **invalid** in general (`R` may mention variables `c` modifies —
valid only under the side condition `mod(c) ∩ fv(R) = ∅`, the HL frame rule);
`{P}c{Q} ⟹ {P∧R}c{Q}` **valid** (`⟦c⟧(P∧R) ⊆ ⟦c⟧P ⊆ Q`);
`{P}c{Q} ⟹ {P}c{Q∧R}` **invalid**;
`{P}c{Q}, {R}c{Q} ⟹ {P∨R}c{Q}` **valid** (`⟦c⟧(P∪R) = ⟦c⟧P ∪ ⟦c⟧R ⊆ Q`);
`{P}c{R}, {R}c{Q} ⟹ {P}c{Q}` **invalid** (`c` runs once, not twice).

### HL.P10 Total correctness: the variant obligations  `[lec 04 / slide 15–28]` ★★
Partial correctness + termination. The `while` rule is strengthened with a **variant**
`t` (an integer expression) and the two proof obligations
`{P ∧ b ∧ t = n} c {P ∧ t < n}` (strictly decreases) and `P ∧ b ⇒ t > 0` (bounded below).
Soundness argument: a strictly decreasing, well-founded, bounded-below measure cannot
decrease infinitely often, so the loop cannot iterate forever. (Lexicographic variants
generalize this to nested loops.) Worked instance: Euclidean division with `t ≜ r`.

---

## 2. Incorrectness Logic — lect. 05–07

### IL.P1 Soundness of IL: every derivable triple is valid  `[lec 07 / slide 6–9]` ★★★
**Th.** `⊢ [P] c [Q]` ⟹ `⟦c⟧P ⊇ Q`.

**Proof.** By induction on the derivation tree; it suffices to show **local soundness**
of every rule (axioms: valid; rules: premises valid ⟹ conclusion valid).
- `[seq]`: from `⟦c₁⟧P ⊇ R` and `⟦c₂⟧R ⊇ Q`,
  `⟦c₁;c₂⟧P = ⟦c₂⟧(⟦c₁⟧P) ⊇ ⟦c₂⟧R ⊇ Q`. ✔
- `[choice]`: from `⟦c₁⟧P ⊇ Q₁` and `⟦c₂⟧P ⊇ Q₂`,
  `⟦c₁+c₂⟧P = ⟦c₁⟧P ∪ ⟦c₂⟧P ⊇ Q₁ ∪ Q₂`. ✔
- `[unroll]`: from `⟦c⋆;c⟧P ⊇ Q`,
  `⟦c⋆⟧P = ⋃_{k≥0} ⟦cᵏ⟧P ⊇ ⋃_{k≥1} ⟦cᵏ⟧P = ⟦c⟧(⋃_{k≥0} ⟦cᵏ⟧P) ⊇ ⟦c⋆;c⟧P ⊇ Q`. ✔ ∎

*Note the direction of every inclusion is simply flipped w.r.t. HL.P1 — the two
soundness proofs are literally the same computation read backwards.*

### IL.P2 Relative completeness of IL  `[lec 07 / slide 10–14]` ★★★
**Th.** Every valid IL triple is derivable, given an oracle to decide implications.

**Proof sketch.** *Go semantic*: assertions are just **sets of states** and implication
is **set inclusion**, so none of HL's finiteness/Gödel obstacles arise.
1. Show `[P] c [⟦c⟧P]` is derivable for every `c, P`, by structural induction on `c`:
   - atomic `e`: this is the axiom `[atom] [P] e [⟦e⟧P]`;
   - `c₁;c₂` and `c₁+c₂`: inductive hypothesis + `[seq]` / `[choice]`;
   - `c⋆` (the interesting case): take `Pₙ ≜ ⟦cⁿ⟧P`, `P₀ = P`. By the IH,
     `[⟦cⁿ⟧P] c [⟦c⟧(⟦cⁿ⟧P)]` and `⟦c⟧(⟦cⁿ⟧P) ≡ ⟦cⁿ;c⟧P ≡ ⟦cⁿ⁺¹⟧P`, i.e.
     `∀n≥0. [Pₙ] c [Pₙ₊₁]`. Rule `[iter]` then gives `[P] c⋆ [∃k. ⟦cᵏ⟧P] ≡ [P] c⋆ [⟦c⋆⟧P]`. ✔
2. Any valid triple satisfies `⟦c⟧P ⊇ Q`, so `[cons]` (**shrink the post**) applied to
   `[P] c [⟦c⟧P]` yields `[P] c [Q]`. ∎

With `ok`/`er` channels, the `er` case of `c⋆` is obtained by instantiating the IH
`∀R. [R] c [er:Q_er]` at `R = ∃k.⟦cᵏ⟧P` and using `[unroll]` on `[P] c⋆;c [er:Q_er]`.

### IL.P3 Hoare's backward assignment axiom is **unsound** for IL  `[lec 05 / slide 23] [lec 06 / slide 48–49]` ★★★
**Claim.** `[Q[a/x]] x:=a [Q]` (sound for HL) is **not** sound for IL.

**Proof (counterexample).** Instance `[y = 42] x := 42 [y = x]`. The state
`δ ≜ [x↦3, y↦3]` satisfies the post `x = y`, but it is **not reachable**: from any
`σ ⊧ (y = 42)`, running `x:=42` gives `y = 42`. So the post does not
under-approximate `⟦x:=42⟧(y=42)`. ∎
Second slide-instance: `[x = y] x := 0 [ok: y = 0]` — `(x↦1, y↦0) ⊧ (y=0)` is
unreachable. Hence IL must use **Floyd's forward** axiom instead.

### IL.P4 `[conj]` is unsound for IL  `[lec 06 / slide 46–47]` ★★★
**Claim.** `[P₁] c [ε:Q₁]`, `[P₂] c [ε:Q₂]` ⟹ `[P₁∧P₂] c [ε:Q₁∧Q₂]` is unsound.

**Proof (counterexample).** `c ≜ x := 7`, `P₁ ≜ (x=0)`, `P₂ ≜ (x=1)`, `Q₁ = Q₂ ≜ (x=7)`.
Both premises are valid. But `P₁ ∧ P₂ ≡ false` and `Q₁ ∧ Q₂ ≡ (x=7)`, and
`[false] x:=7 [ok: x=7]` is **invalid**: `⟦x:=7⟧∅ = ∅ ⊉ (x=7)`. ∎
*(Intuition: an under-approximation cannot conjoin — you would be claiming
reachability from an empty presumption.)*

### IL.P5 Principle of agreement  `[lec 05 / slide 41]` ★★
**Th.** If `[P′] c [Q′]` and `P′ ⇒ P` and `{P} c {Q}`, then `Q′ ⇒ Q`.

**Proof.** `Q′ ⊆ ⟦c⟧P′` (by IL) `⊆ ⟦c⟧P` (by `P′ ⇒ P` + monotonicity) `⊆ Q` (by HL). ∎

### IL.P6 Principle of denial (corollary)  `[lec 05 / slide 43]` ★★
**Cor.** If `[P′] c [Q′]` and `P′ ⇒ P` and `¬(Q′ ⇒ Q)`, then `¬({P} c {Q})`.

**Proof.** Contraposition of IL.P5. ∎
*This is the bridge that lets an IL proof **refute** a Hoare specification: exhibit a
reachable state outside `Q` and the correctness claim is dead.*

### IL.P7 The disj/conj dualities  `[lec 05 / slide 21–22]` ★
**Th.** `[P]c[Q₁] ∧ [P]c[Q₂] ⟺ [P] c [Q₁∨Q₂]`, dually
`{P}c{Q₁} ∧ {P}c{Q₂} ⟺ {P} c {Q₁∧Q₂}`.

**Proof.** (⟹) by `[disj]` / `{conj}`; (⟸) by the respective `[cons]` rule
(IL may **drop disjuncts** in the post since `Q ⊆ Q∨R`; HL may **drop conjuncts**
since `Q∧R ⇒ Q`). ∎

### IL.P8 Mixed HL+IL rules  `[lec 07 / slide 16–19]` ★★
**(a)** `{P∧b} c {P} ⟹ [P] while b do c [ok: P∧¬b]` — **sound, but for a trivial reason:
the conclusion is valid on its own**, whatever the premise. Indeed every `σ ⊧ P ∧ ¬b`
fails the guard immediately, so `σ ∈ ⟦while b do c⟧{σ} ⊆ ⟦while b do c⟧P`; hence
`⟦while b do c⟧P ⊇ P ∧ ¬b`. (Derivable in IL from `[iter0] [P] c⋆ [P]` followed by `¬b?`.)
**(b)** `[P∧b] c [ok:P] ⟹ {P} while b do c {P∧¬b}` — **unsound**.
**Proof (counterexample).** `P = b ≜ (x>0)`, `c ≜ x := x−1`. The IL premise
`[x>0] x:=x−1 [ok: x>0]` is valid (e.g. from `x=2` reach `x=1`). But the HL conclusion
`{x>0} while x>0 do x:=x−1 {x>0 ∧ x≤0} = {x>0} … {false}` is invalid, because the loop
does terminate: `⟦while x>0 do x:=x−1⟧(x>0) ⊄ ∅`. ∎

### IL.P9 The backward-variant `[iter]` rule  `[lec 05 / slide 36–40]` ★
**Rule.** `∀n∈ℕ. [Pₙ] c [Pₙ₊₁]` ⟹ `[P₀] c⋆ [∃k. Pₖ]` (weak form: `[P₀] c⋆ [Pₖ]`).
Soundness is the `[unroll]`/star computation of IL.P1. Instances proved on the slides:
`Pₙ ≜ (x=n)` gives `[x=0] (x:=x+1)⋆ [x = 2⁴²]`;
`Pₙ ≜ (x=2ⁿ)` gives `[x=1] (x:=2×x)⋆ [∃k. x=2ᵏ]`.
Note **no invariant is needed** — a finite unrolling is a witness, because reachability
is existential. In practice `[unroll]` is used, `[iter]` has mostly theoretical value.

---

## 3. Necessary Conditions — lect. 07

### NC.P1 HL/NC duality  `[lec 07 / slide 48–50]` ★★★
**Th.** `{P} c {Q} ⟺ (¬P) c (¬Q)`; equivalently `⟦c⟧P ⊆ Q ⟺ ⟦c⟧ᵒᵖ(¬Q) ⊆ ¬P`.

**Proof (one implication; the other is symmetric).**
Assume `⟦c⟧P ⊆ Q`. We show `⟦c⟧ᵒᵖ(¬Q) ⊆ ¬P`.
Take `σ ∈ ⟦c⟧ᵒᵖ(¬Q)`: there exists `δ ∈ ¬Q` with `σ ∈ ⟦c⟧ᵒᵖδ`, i.e. `δ ∈ ⟦c⟧σ`.
If we had `σ ∈ P`, then `δ ∈ ⟦c⟧σ ⊆ ⟦c⟧P ⊆ Q`, contradicting `δ ∉ Q`.
Hence `σ ∉ P`, i.e. `σ ∈ ¬P`. ∎
**Reading.** NC is HL in the contrapositive: `(P) c (Q)` with `Q` = good outcomes says
*every state that can reach a good outcome is in `P`* — so violating `P` guarantees
(ignoring divergence) failure. HL looks for the **weakest** `P` given `Q` (`wlp`);
NC looks for the **strongest** `P` given `Q`.

### NC.P2 Which consequence rule for NC?  `[lec 07 / slide 46]` ★★
**Th.** NC's `[cons]` is the **IL-shaped** one: `P′ ⇒ P`, `(P′) c (Q′)`, `Q ⇒ Q′` ⟹ `(P) c (Q)`
— *weaken the pre, strengthen the post*.
**Proof (semantic).** Validity is `⟦c⟧ᵒᵖQ ⊆ P`. Shrinking `Q` shrinks `⟦c⟧ᵒᵖQ`
(monotonicity of the pre-image), and enlarging `P` enlarges the right-hand side; both
preserve the inclusion. ∎
*Rule of thumb (slide 42–45): the side carrying the `∀`-over-a-set is the side you may
shrink. `∀` over the pre (HL, SIL) ⟹ strengthen pre / weaken post. `∀` over the post
(IL, NC) ⟹ weaken pre / strengthen post.*

### NC.P3 Trivially valid NC triples  `[lec 07 / slide 53]` ★
**Th.** `(true) c (Q)` and `(P) c (false)` are valid for all `P, Q, c`.
**Proof.** By NC.P1: `(true) c (Q) ⟺ {false} c {¬Q}` ✔ (`⟦c⟧∅ = ∅`), and
`(P) c (false) ⟺ {¬P} c {true}` ✔. ∎ *(These mirror HL's `{false} c {Q}`, `{P} c {true}`.)*

---

## 4. Sufficient Incorrectness Logic — lect. 08

### SIL.P1 Soundness and completeness of SIL  `[lec 08 / slide 33]` ★★
**Th. [Soundness]** Every provable SIL triple is valid (`P ⊆ ⟦c⟧ᵒᵖQ`).
**Th. [Completeness]** Every valid triple is provable, using only the **core** rules.
*The slides state both and defer the proofs to the OOPSLA 2025 paper; the completeness
argument is clean for the same set-theoretic reason as IL.P2 (assertions = sets of
states, implication = inclusion). The proof system is claimed **minimal**.*

### SIL.P2 Manifest errors are exactly the `⟨true⟩`-provable ones  `[lec 08 / slide 25]` ★★★
**Th.** `Q` is a **manifest error** of `c` (an error occurring independently of the
context) `⟺` `⟨true⟩ c ⟨Q⟩` is valid.
**Proof.** Validity of `⟨true⟩ c ⟨Q⟩` unfolds to `∀σ ∈ Σ. ∃δ ∈ Q. δ ∈ ⟦c⟧σ`: *every*
initial state has an execution reaching the error. That is precisely the definition of
"the error occurs regardless of the context". ∎
**Contrast.** IL **cannot** characterize manifest errors: `[true] c [er: Q]` only says
each error state is reachable from *some* input, not from every input.

### SIL.P3 `⟨conj⟩` is unsound for SIL  `[lec 08 / slide 42–43]` ★★★
**Proof (counterexample).** With `x := nondet()`:
`⟨x=0⟩ x:=nondet() ⟨x=0⟩` and `⟨x=0⟩ x:=nondet() ⟨x=1⟩` are both valid (from `x=0`
*some* execution yields `x=0`, and *some* yields `x=1`). `⟨conj⟩` would derive
`⟨x=0⟩ x:=nondet() ⟨false⟩`, which is invalid (no execution reaches `∅`). ∎
*(Same shape as IL.P4: existential post-conditions do not conjoin.)*

### SIL.P4 The **forward** assume axiom is invalid in SIL  `[lec 08 / slide 44–45]` ★★★
**Claim.** `⟨P⟩ b? ⟨P ∧ b⟩` is **not** valid (the sound one is the backward
`⟨assume⟩ ⟨Q ∧ b⟩ b? ⟨Q⟩`).
**Proof (counterexample).** `⟨x ≥ 0⟩ (x > 1)? ⟨x ≥ 2⟩`. Instance of the schema with
`P ≜ x≥0`, `b ≜ x>1` (over ℤ, `P∧b ≡ x≥2`). It is invalid: the state `x = 0` satisfies
the precondition but `⟦(x>1)?⟧{x=0} = ∅`, so it reaches no state of the post. ∎
*Moral: SIL's pre must contain **only** states that really trigger the post; a guard
filters states away, so it must be applied backwards.*

### SIL.P5 SIL ≡ HL on deterministic, terminating programs  `[lec 08 / slide 39]` ★★
**Th.** If `c` is deterministic and always terminates, `⟨P⟩ c ⟨Q⟩ ⟺ {P} c {Q}`.
**Proof.** Determinism + termination means `⟦c⟧σ` is a **singleton** `{δ_σ}` for every `σ`.
Then SIL validity `∀σ∈P. ∃δ∈Q. δ ∈ ⟦c⟧σ` becomes `∀σ∈P. δ_σ ∈ Q`, which is exactly
HL validity `∀σ∈P. ∀δ∈⟦c⟧σ. δ ∈ Q`. ∎
*(The four quadrants collapse pairwise when `⟦c⟧` is a total function: ∃ = ∀ on singletons.)*

### SIL.P6 SIL vs IL — where the path condition lives  `[lec 08 / slide 37–38]` ★★
For `c₄₂ ≜ if even(x) { if odd(y) { z := 42 } }` and error spec `Q ≜ (z = 42)`:
- IL proves `[z=11] c₄₂ [er: z=42 ∧ odd(y) ∧ even(x)]` — the path condition ends up in
  the **post**, so the triple certifies reachability but does not name the culprits.
- SIL proves `⟨z=11 ∧ odd(y) ∧ even(x)⟩ c₄₂ ⟨z=42⟩` — the path condition is in the
  **pre**: these are precisely the **responsible inputs**.
- With `x := nondet()` prepended, HL only manages `{z=42} c₄₂ {z=42}` while SIL gives
  `⟨odd(y)⟩ c₄₂ ⟨z=42⟩`.

### SIL.P7 Trivially valid SIL triples  `[lec 08 / slide 41]` ★
`⟨false⟩ c ⟨R⟩` ✔ (vacuous `∀σ ∈ ∅`) · `⟨true⟩ c ⟨true⟩` ✔ if `c` has at least one
execution from every state · `⟨R⟩ c⋆ ⟨R ∨ x=0⟩` ✔ (take `0` iterations) ·
`⟨wlp(c,R)⟩ c ⟨R⟩` ✔ (every state whose runs all land in `R` certainly has *one*).

---

## 5. Separation Logic — lect. 09–10

### SL.P1 Correctness (soundness) of SL  `[lec 10 / slide 27]` ★★
**Th.** If `⊢ {P} c {Q}` then `⟦c⟧P ⊆ Q`, over states `σ = ⟨s,h⟩` with the relational
semantics of slide 26 (`x := [a]`, `[a₁] := a₂`, `alloc`, `free`, `cons`).
**Proof.** By induction on the derivation — same schema as HL.P1, with the local axioms
as base cases and the **frame rule** `{P} c {Q} ⟹ {P∗R} c {Q∗R}`
(side condition `mod(c) ∩ fv(R) = ∅`) handled by the disjointness of the heap split. ∎

### SL.P2 Incompleteness of SL — the footprint property fails  `[lec 10 / slide 36–41]` ★★★
**Th.** There exist **valid** SL triples that are **not provable**.

**Proof (counterexample).** We would like to derive the valid
`{y ↦ _} x := alloc(); free(x) {y ↦ _ ∧ y ≠ x}`.
The *footprint recipe* is: derive the spec with the local axioms, then close with `[frame]`.
Doing so:

```
{y ↦ _ ∗ emp}
  {emp}                     x := alloc()      {∃v. v ↦ _ ∧ x = v}
  {x ↦ _}                   free(x)           {emp}          ← lossy!
{∃v. y ↦ _ ∧ x = v}         // strongest derivable spec
```
The `free` axiom `{x ↦ _} free(x) {emp}` **forgets that `x` ever held a location**, so
`y ≠ x` can no longer be derived: the derivable post is strictly weaker than the valid one. ∎

**Diagnosis (slide 41).** The local axioms let resources **grow** (`alloc`) and **shrink**
(`free`); *the model should never let them silently shrink*. This is exactly what ISL
repairs with `x ↦̸` (ISL.P2–P3).

### SL.P3 A state satisfying `(x↦y) ∗ ¬(x↦y)`  `[lec 10 / slide 32–33]` ★
**Proof (witness).** `s(x)=11, s(y)=42`, `h = [11 ↦ 42]`. Split `h = h₁ • h₂` with
`h₁ = [11↦42]` (satisfies `x↦y`) and `h₂ = []` (the **empty** heap satisfies `¬(x↦y)`,
since `x↦y` requires `dom(h) = {s(x)}`). ∎ *(`∗` splits the heap, not the store —
so the same `x` may be described twice.)*

### SL.P4 The *imprecise* list segment is not `ls`  `[lec 10 / slide 34–35]` ★★
**Claim.** `ils(a₁,a₂) ≜ (a₁=a₂ ∧ emp) ∨ (∃v. a₁↦v ∗ ils(v,a₂))` is **not** equivalent to
`ls(a₁,a₂) ≜ (a₁=a₂ ∧ emp) ∨ (a₁≠a₂ ∧ ∃v. a₁↦v ∗ ls(v,a₂))`.
**Proof (witness).** `h = [42 ↦ 42]` (a self-loop cell). Then `⟨s,h⟩ ⊧ ils(42,42)` via the
second disjunct with `v = 42` (and `ils(42,42)` again on the empty remainder — the
missing `a₁≠a₂` guard makes the unfolding non-terminating/imprecise), whereas
`⟨s,h⟩ ⊭ ls(42,42)`: `ls(42,42)` forces `emp`, but `h ≠ []`. ∎

---

## 6. Incorrectness Separation Logic (ISL) — lect. 10

### ISL.P1 The naive frame rule is **unsound** with SL's `free` axiom  `[lec 10 / slide 51–52]` ★★★
**Claim.** Taking `[x ↦ v] free(x) [ok: emp]` (the direct IL-ification of SL's axiom)
breaks the frame rule.
**Proof (derivation of an invalid triple).**

```
                [x ↦ v] free(x) [ok: emp]                        [free]
  ────────────────────────────────────────────────────────       [frame]  (R ≜ x ↦ v)
  [x ↦ v ∗ x ↦ v] free(x) [ok: emp ∗ x ↦ v]
  ────────────────────────────────────────────────────────       [cons]
  [false] free(x) [ok: x ↦ v]
```
`x↦v ∗ x↦v ≡ false` (a cell cannot be split from itself), and `emp ∗ x↦v ≡ x↦v`.
The conclusion `[false] free(x) [ok: x↦v]` is **invalid**: `⟦free(x)⟧∅ = ∅ ⊉ (x↦v)`.
The only sound under-approximate post of `false` is `false`. ∎
**Cause.** `free` **shrinks** the resource; in an under-approximate setting the frame
must be re-attachable, and a shrinking heap makes the framed-in cell reappear from nothing.

### ISL.P2 The fix: the deallocated-cell predicate `x ↦̸` (monotonic heap)  `[lec 10 / slide 53–56]` ★★★
**Definition.** `⟨s,h⟩ ⊧ x ↦̸` iff `dom(h) = {s(x)}` and `h(s(x)) = ⊥`.
Consequently `x ↦ v ∗ x ↦̸ ≡ false ≡ x ↦̸ ∗ x ↦̸`, and `y↦v ∗ x↦̸ ≡ y↦v ∗ x↦̸ ∧ x≠y`.
New axiom: `[x ↦ v] free(x) [ok: x ↦̸]` — *resources never shrink*.
**Proof that the frame derivation is now sound.**

```
                [x ↦ v] free(x) [ok: x ↦̸]                        [free]
  ─────────────────────────────────────────────────────────      [frame]
  [x ↦ v ∗ x ↦ v] free(x) [ok: x ↦̸ ∗ x ↦ v]
  ─────────────────────────────────────────────────────────      [cons]
  [false] free(x) [ok: false]
```
because `x ↦̸ ∗ x ↦ v ≡ false`. The conclusion `[false] free(x) [ok: false]` is a **sound**
under-approximation. ∎

### ISL.P3 The footprint property **holds** in ISL  `[lec 10 / slide 57, 62]` ★★★
**Th. [footprint / completeness]** Every valid ISL triple `[σ_P] c [ε: σ_Q]` can be derived.
**Proof (the counterexample of SL.P2, now derivable).**

```
[y ↦ _ ∗ emp]
  [emp]      x := alloc()   [x ↦ v]
  [x ↦ v]    free(x)        [x ↦̸]
[ok: y ↦ _ ∗ x ↦̸ ∧ y ≠ x]
```
The `↦̸` cell is still *owned*, so `∗` forces `y ≠ x` — the information SL had lost is
retained, and the strongest valid post is now derivable. (The general theorem is proved
in the CAV 2020 paper.) ∎

### ISL.P4 Correctness (soundness) of ISL  `[lec 10 / slide 62]` ★★
**Th.** If `⊢ [P] c [ε: Q]` then `Q ⊆ ⟦c⟧ε(P)`, w.r.t. the `ok`/`er` relational semantics
of slide 60. **Proof.** By induction on the derivation. ∎
**Corollary (no-false-positives).** Every bug ISL reports is real: an `er` post that is
not `false` is a genuinely reachable crash state.

### ISL.P5 `[∗conj]` is unsound  `[lec 10 / slide 67–68]` ★★★
**Claim.** `[P₁] c [Q₁]`, `[P₂] c [Q₂]` ⟹ `[P₁ ∗ P₂] c [Q₁ ∗ Q₂]` is unsound.
**Proof (counterexample).** It suffices to use **pure** assertions, for which `P ∗ Q ≡ P ∧ Q`.
Take `[x=0] x:=1 [x=1]` and `[x=1] x:=1 [x=1]` (both valid). `[∗conj]` would derive
`[false] x:=1 [x=1]`, invalid as in IL.P4. ∎

### ISL.P6 Soundness of the write axiom  `[lec 10 / slide 65–66]` ★
**Claim.** `[x ↦ _] [x] := y [ok: x ↦ y]` is sound.
**Proof.** From the local axiom `[x ↦ v] [x]:=y [ok: x ↦ y]` and `(x ↦ v) ⇒ (x ↦ _)`,
apply IL's `[cons]` (**weaken the pre**, keep the post):

```
(x ↦ v) ⇒ (x ↦ _)      [x ↦ v] [x] := y [ok: x ↦ y]
────────────────────────────────────────────────────
        [x ↦ _] [x] := y [ok: x ↦ y]
```
∎ *(Legal precisely because IL/ISL's consequence rule weakens the pre — the opposite of HL.)*

### ISL.P7 The error axioms  `[lec 10 / slide 51, 55, 58]` ★★
Sound by direct inspection of the `er` semantics (slide 60):
null-deref `[x = nil] [x]:=y [er: x = nil]`, `[y = nil] x:=[y] [er: y = nil]`;
use-after-free `[x ↦̸] [x]:=y [er: x ↦̸]`, `[y ↦̸] x:=[y] [er: y ↦̸]`;
double-free `[x ↦̸] free(x) [er: x ↦̸]`;
reuse of a deallocated location `[y ↦̸] x:=alloc() [ok: x↦v ∧ x=y]`.

---

## 7. Separation SIL (SepSIL) — lect. 10

### SepSIL.P1 Correctness + (relative) completeness  `[lec 10 / slide 86]` ★★
**Th. [correctness]** If `⊢ ⟨P⟩ c ⟨Q⟩` then `P ⊆ ⟦c⟧ᵒᵖQ`. **Proof.** By induction on the
derivation (w.r.t. the relational semantics of slide 84). ∎
**Th. [completeness]** Every valid triple `⟨P⟩ c ⟨Q⟩` can be derived. **Proof.** See the
OOPSLA 2025 paper — the completeness hinges on the assertion language carrying `↦̸` and on
the atomic rules being **weakest-precondition-precise** (backward axioms "speak precisely",
so they apply to *any* post).

### SepSIL.P2 Why SepSIL beats ISL on the same bug  `[lec 10 / slide 78–82]` ★★
On the use-after-free client (`push_back` / `client(v)`), ISL derives a long `er` post
listing the reachable crash states, whereas SepSIL derives a **more succinct
postcondition** and a **stronger guarantee**: *any* state in the pre can drive `c` into
the memory error (source characterization), rather than merely *the error post is reachable*.

### SepSIL.P3 Which SepSIL triples are valid?  `[lec 10 / slide 88]` ★
`⟨emp⟩ free(x) ⟨x ↦̸⟩` ✘ (you cannot free what you do not own: from `emp` the command
faults) · `⟨x ↦̸⟩ free(x) ⟨x ↦̸⟩` ✘ under the `ok` semantics (double free is an error, not
a normal termination) · `⟨false⟩ free(x) ⟨emp⟩` ✔ (vacuously) ·
`⟨x ↦ _⟩ free(x) ⟨emp⟩` ✘ — the sound axiom is `⟨x ↦ _⟩ free(x) ⟨x ↦̸⟩`
(the heap is **monotonic**: the cell stays, marked deallocated).

---

## Recurring proof patterns (worth memorizing)

1. **Soundness of a forward logic** = push the semantics through `[seq]`/`[choice]`/`[iter]`
   and check the inclusion direction survives: HL.P1 and IL.P1 are the *same* computation
   with `⊆` flipped to `⊇`.
2. **Unsoundness of `conj`** (IL.P4, SIL.P3, ISL.P5) = pick two triples with contradictory
   pres, conjoin to `false`, and observe `⟦c⟧∅ = ∅` cannot over-…/under-approximate a
   non-empty post. One counterexample, three logics.
3. **Wrong assignment axiom** (IL.P3) = exhibit a state satisfying the post that is
   **unreachable** from the pre.
4. **Frame unsoundness** (ISL.P1) = frame a resource the command *destroys*; fix by never
   shrinking the heap (`↦̸`).
5. **Incompleteness** = either a computability argument (HL.P5/P6) or an
   information-loss counterexample (SL.P2).
