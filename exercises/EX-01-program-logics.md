# Exercises — Program Logics (HL · IL · NC · SIL · SL · ISL · SepSIL)

> All exercises extracted from the lecture slides (lectures 03–10) plus the
> matching items from the exam exercise sheets. Statements are given first;
> the **Answer** / **Solution** blocks reproduce what the slides (or the
> solution sheet) provide. Source is noted as `[lec NN / slide M]`.
> See also the per-logic overviews in [`../overviews/`](../overviews/README.md).

Notation: `⟦c⟧P` forward image, `⟦c⟧ᵒᵖQ` backward pre-image (Hoare's *weakest
possible precondition* `wpp`), `wlp(c,Q)` weakest liberal precondition.

---

## 1. Hoare Logic (HL) — lect. 03

### HL.1 Validity warm-up  `[lec 03 / slide 44]`
A HL triple `{P} c {Q}` is valid iff `⟦c⟧P ⊆ Q`.
- Is `{x > 0} x := 10x {x > 10}` valid?
- Is `{x > 0, y > 0} x := yx {x ≥ 0}` valid?
- For which `Q` is `{false} c {Q}` valid? For which `P` is `{P} c {true}` valid?

### HL.2 Is the `[frame/conj]` rule valid in HL?  `[lec 03 / slide 45]`
```
        {P} c {Q}
   ────────────────────
   {P ∧ R} c {Q ∧ R}
```

### HL.3 Is this rule valid in HL?  `[lec 03 / slide 46]`
```
      {P} c {Q}
   ────────────────
   {P ∧ R} c {Q}
```

### HL.4 Is this rule valid in HL?  `[lec 03 / slide 47]`
```
      {P} c {Q}
   ────────────────
   {P} c {Q ∧ R}
```

### HL.5 Is this rule valid in HL?  `[lec 03 / slide 48]`
```
   {P} c {Q}   {R} c {Q}
   ─────────────────────
      {P ∨ R} c {Q}
```

### HL.6 Is this (composition) rule valid in HL?  `[lec 03 / slide 49]`
```
   {P} c {R}   {R} c {Q}
   ─────────────────────
        {P} c {Q}
```

### HL.7 Derivation: max  `[lec 06 / slide 37–38]`
Find a derivation for the HL triple
`{true} if x ≥ y then z := x else z := y {z = max(x, y)}`.

**Solution.**
```
{true}
if x ≥ y then
   {x ≥ y}   z := x   {z = x ≥ y} ⇒ {z = max(x,y)}
else
   {y > x}   z := y   {z = y > x} ⇒ {z = max(x,y)}
{z = max(x, y)}
```

### HL.8 Prove that `{conj}` is sound  `[lec 06 / slide 39–40]`
```
   {P₁} c {Q₁}   {P₂} c {Q₂}
   ─────────────────────────  {conj}
     {P₁ ∧ P₂} c {Q₁ ∧ Q₂}
```
**Solution.** Assume `⟦c⟧P₁ ⊆ Q₁` and `⟦c⟧P₂ ⊆ Q₂`. By monotonicity of `⟦c⟧`,
`⟦c⟧(P₁∧P₂) ⊆ ⟦c⟧P₁ ⊆ Q₁` and `⟦c⟧(P₁∧P₂) ⊆ ⟦c⟧P₂ ⊆ Q₂`. Hence
`⟦c⟧(P₁∧P₂) ⊆ Q₁ ∧ Q₂`. ∎

### HL.9 Show the "syntactic replacement" assignment rule is **unsound**  `[lec 06 / slide 41–42]`
Show that `{P} x := a {P[a/x]}` (forward substitution) is not sound.

**Solution.** Take the instance `{y = x} x := 0 {y = 0}`. Then
`⟦x := 0⟧[x↦1, y↦1] = [x↦0, y↦1] ⊭ {y = 0}`. ∎

---

## 2. Incorrectness Logic (IL) — lect. 05–07

### IL.1 Complete-and-prove the loop triple  `[lec 05 / slide 47]`
```
[true]
n := nondet();
x := 0;
while (n > 0) do
   x := x + n;
   n := nondet();
[?]
```
Complete the postcondition `[?]` and prove the IL triple.

**Solution.** The postcondition is `[ok: x ≥ 0 ∧ n ≤ 0]`, which is *exactly*
`⟦c⟧true` (the strongest post — hence the triple is simultaneously HL-valid).

*Why this set.* The loop exits only through `¬b ≡ n ≤ 0`, and the last thing the
body does is `n := nondet()`, so on exit `n` is any value `≤ 0`. `x` accumulates
a sum of strictly positive values: `0` iterations gives `x = 0`; one iteration
gives *any* `x > 0` (choose `n₀ = x`); further iterations add nothing new. So the
reachable set is exactly `x ≥ 0 ∧ n ≤ 0`.

*Derivation.* Write `b ≜ (n > 0)` and `c_body ≜ (x := x + n; n := nondet())`.

```
[true]
n := nondet();                     [nondet]  [∃n. true] ≡ [true]
x := 0;                            [Floyd]   [∃x′. true ∧ x = 0] ≡ [x = 0] ≜ P₀
while (n > 0) do
   x := x + n;
   n := nondet();
[ok: x ≥ 0 ∧ n ≤ 0]                [iter]
```

Take the family (**no invariant needed** — one assertion per unrolling depth):

```
P₀ ≜ (x = 0)            P_k ≜ (x ≥ k)   for k ≥ 1
```

and discharge every premise `[P_k ∧ b] c_body [P_{k+1}]` by Floyd + `[nondet]`:

```
k = 0:  [x = 0 ∧ n > 0]  x := x+n  [∃x′. x′=0 ∧ n>0 ∧ x = x′+n] ≡ [x = n ∧ n > 0]
                         n := *    [∃n. x = n ∧ n > 0]           ≡ [x ≥ 1] = P₁ ✔

k ≥ 1:  [x ≥ k ∧ n > 0]  x := x+n  [∃x′. x′≥k ∧ n>0 ∧ x = x′+n] ≡ [x ≥ k+1 ∧ 0 < n ≤ x−k]
                         n := *    [∃n. …]                       ≡ [x ≥ k+1] = P_{k+1} ✔
```

(Each step is an *equality* with the image, so the IL side condition `Q ⊆ ⟦c⟧P`
holds trivially.) The iteration rule then yields

```
[P₀] while b do c_body [ok: (∃k. P_k) ∧ ¬b]
   with  ∃k. P_k  ≡  (x = 0) ∨ (x ≥ 1)  ≡  x ≥ 0
   and   ¬b       ≡  n ≤ 0
```

Sequencing with the two initial assignments gives `[true] c [ok: x ≥ 0 ∧ n ≤ 0]`. ∎

*Shortcut.* The one-unrolling derived rule `[P₀ ∧ b] c [P₁] ⟹ [P₀] while b do c
[(P₀ ∨ P₁) ∧ ¬b]` already suffices here: with `P₀ ≜ (x = 0)` and `P₁ ≜ (x > 0)`
it gives `[(x = 0 ∨ x > 0) ∧ n ≤ 0] ≡ [x ≥ 0 ∧ n ≤ 0]` directly.

*Remarks.*
- Any **subset** of the image is also a valid IL post (`[cons]` may shrink the
  post): `[ok: x > 0 ∧ n ≤ 0]` and even `[ok: false]` are valid but uninformative.
  The exercise asks for the *strongest* one.
- Dropping the `n ≤ 0` conjunct makes the triple **invalid**: `[ok: x ≥ 0]` would
  claim states with `n > 0` are reachable at exit, and they are not.

### IL.2 Which triples are valid (for any `c`, `R`)?  `[lec 06 / slide 43]`
Compare each IL triple with the analogous HL triple:
- `[R] c [ok:false][er:false]`   vs `{R} c {false}`
- `[R] c [ok:true]`              vs `{R} c {true}`
- `[true] c [ok:R]`              vs `{false} c {R}`
- `[wlp(c,R)] c [ok:R]`          vs `{wlp(c,R)} c {R}`

**Solution.** Recall `[P] c [ε:Q]` valid iff `Q ⊆ ⟦c⟧ε P`, and `{P} c {Q}` valid
iff `⟦c⟧P ⊆ Q`. **Three of the four HL triples are universally valid; only one of
the IL ones is.**

| # | IL triple | valid? | HL triple | valid? |
|---|---|---|---|---|
| 1 | `[R] c [ok:false][er:false]` | **always** | `{R} c {false}` | iff `c` never terminates from `R` |
| 2 | `[R] c [ok:true]` | iff `⟦c⟧ok R = Σ` (≈ never) | `{R} c {true}` | **always** |
| 3 | `[true] c [ok:R]` | iff `R ⊆ ⟦c⟧ok Σ` | `{false} c {R}` | **always** |
| 4 | `[wlp(c,R)] c [ok:R]` | **no** (in general) | `{wlp(c,R)} c {R}` | **always** |

1. `false ≡ ∅ ⊆ ⟦c⟧ε R` holds for every `c, R, ε`: an IL triple with a `false`
   post is **trivially valid and says nothing**. (This is why an `er` post must be
   *satisfiable* to prove a bug.) In HL the same post is the *strongest* possible
   claim: `⟦c⟧R ⊆ ∅` says `c` diverges (or errors) on all of `R`.
2. Mirror image. `true ≡ Σ ⊆ ⟦c⟧ok R` demands that **every** state be reachable —
   false e.g. for `c ≜ skip`, `R ≜ false` (`⟦skip⟧∅ = ∅ ⊉ Σ`). In HL `{R} c {true}`
   is the trivially-valid one.
3. `[true] c [ok:R]` requires every state of `R` to be reachable from *some* input.
   Counterexample: `c ≜ x := 0`, `R ≜ (x = 1)` — nothing reaches `x = 1`. In HL,
   `{false} c {R}` is trivially valid (`⟦c⟧∅ = ∅ ⊆ R`).
4. `{wlp(c,R)} c {R}` is valid **by definition** of `wlp` (the weakest pre
   guaranteeing `R`). The IL reading needs `R ⊆ ⟦c⟧(wlp(c,R))`, which fails:
   take `c ≜ x := 0` and `R ≜ (x = 0 ∨ x = 1)`. Then `wlp(c,R) = true`, but
   `⟦c⟧true = (x = 0) ⊉ R` — the state `x = 1` satisfies the post and is
   **unreachable**. (Simpler still: `c` diverging ⇒ `wlp(c,R) = true` and
   `⟦c⟧true = ∅`.) `wlp` is *not* the IL precondition; the IL-side analogue is the
   **weakest possible precondition** `wpp = ⟦c⟧ᵒᵖR` (see NC.1), and even
   `[⟦c⟧ᵒᵖR] c [ok:R]` is valid only when every state of `R` has a predecessor —
   i.e. condition 3 again.

**Slogan.** HL is trivialised by a `false` **pre** or a `true` **post**; IL is
trivialised only by a `false` **post**. In IL a `true` pre is the *hardest* claim
to make, not the easiest — exactly the reversal of `[cons]`.

### IL.3 Derivation: max  `[lec 06 / slide 44–45]`
Find a derivation for `[true] if x ≥ y then z := x else z := y [ok: z = max(x,y)]`.

**Solution.**
```
[true]
if x ≥ y then
   [x ≥ y]   z := x   [z = x ≥ y] ≡ [x ≥ y, z = max(x,y)]
else
   [y > x]   z := y   [z = y > x] ≡ [y > x, z = max(x,y)]
[ok: z = max(x, y)]
```
(Note the branch pre `[y > x]` — not `[x < y]` — because in IL the post of a
guard must be genuinely reachable.)

### IL.4 Prove `[conj]` is **not** sound  `[lec 06 / slide 46–47]`
```
   [P₁] c [ε:Q₁]   [P₂] c [ε:Q₂]
   ─────────────────────────────  [conj]
     [P₁ ∧ P₂] c [ε:Q₁ ∧ Q₂]
```
**Solution.** Take `c ≜ x := 7`, `P₁ ≜ (x=0)`, `P₂ ≜ (x=1)`, `Qᵢ ≜ (x=7)`. Both
premises are valid, but `P₁∧P₂ ≡ false` and `[false] x := 7 [ok: x=7]` is invalid
since `⟦x:=7⟧false = ∅ ⊉ (x=7)`. ∎

### IL.5 Show the forward-substitution assignment rule is **unsound** for IL  `[lec 06 / slide 48–49]`
Show `[P] x := a [ok: P[a/x]]` is not sound.

**Solution.** Instance `[x = y] x := 0 [ok: y = 0]`. The state `(x↦1, y↦0) ⊨ (y=0)`
but it is **not reachable** by `x := 0`, so the post over-shoots the image. ∎

### IL.6 Mixed HL+IL rule 1 — sound?  `[lec 07 / slide 16–17]`
```
        {P ∧ b} c {P}
   ─────────────────────────
   [P] while b do c [ε: P ∧ ¬b]
```
**Answer.** Valid — the conclusion is always valid (recall the IL loop rules
`[P₀∧b] c [P₁] ⟹ [P₀] while b do c [(P₀∨P₁)∧¬b]`).

### IL.7 Mixed HL+IL rule 2 — sound?  `[lec 07 / slide 18–19]`
```
       [P ∧ b] c [ε: P]
   ─────────────────────────
   {P} while b do c {P ∧ ¬b}
```
**Answer.** Not sound. Take `P = b ≜ (x>0)`, `c ≜ x := x−1`. The IL premise
`[x>0] x:=x−1 [ε: x>0]` is valid, but `{x>0} x:=x−1 {false}` is invalid because
`⟦x:=x−1⟧(x>0) ⊄ ∅`.

---

## 3. Necessary Conditions (NC) — lect. 07

### NC.1 `wlp` vs `wpp`  `[lec 07 / slide 52]`
Let `c ≜ (z := x) + (z := y)` and `Q ≜ (z = 0)`.
- What is `wlp(c, Q)`?  (answer: `x = 0 ∨ y = 0`)
- What is `⟦c⟧ᵒᵖQ`?    (answer: `x = 0 ∨ y = 0`)

*(Compare with the deterministic case where they coincide with `x = y = 0`.)*

### NC.2 Validity of NC triples via the HL duality  `[lec 07 / slide 53]`
Recall both `{false} c {Q}` and `{P} c {true}` are valid HL triples for any
`P, Q, c`. Using the duality `(P) c (Q) ⟺ {¬P} c {¬Q}`, what can you claim
about the validity of NC triples such as `(P) c (true)` and `(false) c (Q)`?

**Answer (guide).** `(P) c (⊤) ⟺ {¬P} c {⊥}` and `(⊥) c (Q) ⟺ {⊤} c {¬Q}`;
transpose the two "always valid" HL facts through the contrapositive.

---

## 4. Sufficient Incorrectness Logic (SIL) — lect. 08

Triple `⟨P⟩ c ⟨Q⟩` valid iff `P ⊆ ⟦c⟧ᵒᵖQ` (∀σ∈P. ∃δ∈Q. δ∈⟦c⟧σ).

### SIL.1 Which SIL triples are valid (for any `c`, `R`)?  `[lec 08 / slide 41]`
- `⟨false⟩ c ⟨R⟩`
- `⟨false⟩ c ⟨false⟩`
- `⟨R⟩ c⋆ ⟨R ∨ x = 0⟩`
- `⟨wlp(c,R)⟩ c ⟨R⟩`

### SIL.2 Prove `⟨conj⟩` is unsound for SIL  `[lec 08 / slide 42–43]`
```
   ⟨P₁⟩ c ⟨Q₁⟩   ⟨P₂⟩ c ⟨Q₂⟩
   ─────────────────────────  ⟨conj⟩
     ⟨P₁ ∧ P₂⟩ c ⟨Q₁ ∧ Q₂⟩
```
**Solution.** With nondeterministic assignment `x := nondet()`: the triples
`⟨x=0⟩ x:=* ⟨x=0⟩` and `⟨x=0⟩ x:=* ⟨x=1⟩` are valid, so `⟨conj⟩` would give
`⟨x=0⟩ x:=* ⟨x=0 ∧ x=1⟩ = ⟨x=0⟩ x:=* ⟨false⟩`, which is not sound. ∎

### SIL.3 Prove/disprove the forward guard axiom in SIL  `[lec 08 / slide 44–45]`
Is `⟨P⟩ b? ⟨P ∧ b⟩` valid?

**Solution.** Not valid. Counterexample `⟨x ≥ 0⟩ (x > 1)? ⟨x ≥ 2⟩`: from `x = 0`
we cannot reach `x ≥ 2`. (The *backward* guard axiom `⟨Q ∧ b⟩ b? ⟨Q⟩` is the
sound one for SIL.) ∎

---

## 5. Separation Logic assertions (SL) — lect. 09–10

State `⟨s, h⟩`: store `s: X→ℤ`, heap `h: N ⇀ ℤ⊥`. `a₁↦a₂` = single owned cell;
`emp` = empty heap; `*` = separating conjunction; `a₁ ≐ a₂ ≜ (a₁=a₂) ∧ emp`.

### SL.1 Satisfaction 1  `[lec 10 / slide 30–31]`
Find a state satisfying each assertion (or argue none exists):
- `(x ≐ y) * x ↦ y`
- `(x = y) * x ↦ y`
- `(x = y) ∧ x ↦ y`
- `x ↦ x`

**Answer sketch.** `(x≐y)*x↦y`: store with `s(x)=s(y)`, heap one cell at `x`
holding `y`. `(x=y)∧x↦y`: same single cell with `s(x)=s(y)`. `x↦x`: a cell at
location `s(x)` whose contents equal `s(x)`.

### SL.2 Satisfaction 2  `[lec 10 / slide 32–33]`
Show a state satisfying `(x ↦ y) * ¬(x ↦ y)`.

**Solution.** `dom(h) = {11}`, `s(x)=11`, `h(11)=42`, `s(y)=42`. Split the
(single-cell) heap: one part is `x↦y`, the *other* part is empty and empty ⊨ ¬(x↦y).

### SL.3 List segments: `ils` ≠ `ls`  `[lec 10 / slide 34–35]`
With the imprecise segment `ils(a₁,a₂) ≜ (a₁=a₂ ∧ emp) ∨ (∃v. a₁↦v * ils(v,a₂))`
and the precise `ls(a₁,a₂) ≜ (a₁=a₂ ∧ emp) ∨ (a₁≠a₂ ∧ ∃v. a₁↦v * ls(v,a₂))`,
find a state satisfying `ils(42,42)` but not `ls(42,42)`.

**Solution.** `dom(h)={42}`, `h(42)=42` (a self-loop cell). Then `⟨s,h⟩ ⊨ ils(42,42)`
(take `v=42`) but `⟨s,h⟩ ⊭ ls(42,42)` (the disjunct needs `a₁≠a₂`). ∎

---

## 6. Incorrectness Separation Logic (ISL) — lect. 10

### ISL.1 Is the store axiom sound?  `[lec 10 / slide 65–66]`
Is `[x ↦ _] [x] := y [ok: x ↦ y]` sound?

**Solution.** Yes. From the strongest small axiom `[x↦v] [x]:=y [ok: x↦y]`, since
`(x↦v) ⇒ (x↦_)`, `[cons]` gives `[x↦_] [x]:=y [ok: x↦y]`. ∎

### ISL.2 Prove `[*conj]` is unsound  `[lec 10 / slide 67–68]`
```
   [P₁] c [Q₁]   [P₂] c [Q₂]
   ─────────────────────────  [*conj]
     [P₁ * P₂] c [Q₁ * Q₂]
```
**Solution.** It suffices to use pure assertions (`P*Q ≡ P∧Q`). Consider
`[x=0] x:=1 [x=1]` and `[x=1] x:=1 [x=1]`; `[*conj]` would derive
`[false] x:=1 [x=1]`, unsound. ∎

### ISL.3 (Exam sheet B, Ex. 1) ISL derivation with free / alloc  `[sheet b]`
For the code `c`:
```
x := [y];
if (x != nil) then { free(y); y := x; }
else            { x := alloc(); [y] := x; }
```
Using ISL, find a suitable (non-trivial) postcondition `Q` for the triple
`[y ↦ z * z ↦ nil] c [ok : Q]` and inline the intermediate derivation steps.

---

## 7. Separation SIL (SepSIL) — lect. 10

Triple `⟨P⟩ c ⟨Q⟩` with heap + frame; `x ↦̸` = tracked-deallocated cell.

### SepSIL.1 Which SepSIL triples are valid?  `[lec 10 / slide 88]`
- `⟨emp⟩ free(x) ⟨x ↦̸⟩`
- `⟨x ↦̸⟩ free(x) ⟨x ↦̸⟩`
- `⟨false⟩ free(x) ⟨emp⟩`
- `⟨x ↦ _⟩ free(x) ⟨emp⟩`

### SepSIL.2 "Compiling" to SepSIL syntax  `[lec 10 / slide 90–91]`
Rewrite the C-like code into the regular-command syntax:
`i := 0; q := *p; while (q ≠ nil) do { q := *q; i := i + 1 }`.

**Solution.**
```
i := 0 ;
q := [p] ;
( (q ≠ nil?) ; q := [q] ; i := i + 1 )⋆ ;
(q = nil?)
```

### SepSIL.3 Reasoning: prove `⟨p ↦ nil * true⟩ c ⟨i = 0⟩`  `[lec 10 / slide 92–93]`
where `c ≜ i := 0; q := *p; while (q ≠ nil) do { q := *q; i := i+1 }`.

**Solution.**
```
⟨p ↦ nil * true⟩ ⇒ ⟨v = nil * p ↦ v⟩
i := 0 ;
⟨i = 0 ∧ v = nil * p ↦ v⟩
q := [p] ;
⟨i = 0 ∧ q = nil * p ↦ v⟩ ⇒ ⟨i = 0 ∧ q = nil⟩
( (q ≠ nil?) ; q := [q] ; i := i + 1 )⋆ ;
⟨i = 0 ∧ q = nil⟩
(q = nil?)
⟨i = 0⟩
```

### SepSIL.4 Validate the ISL / SepSIL push-back derivations  `[lec 10 / slide 89]`
Re-check the PB-Ok / PB-Client proof sketches from Raad et al. (Fig. 3): the
`free(y)` step yields `a ↦̸`, the store into a freed cell (`StoreEr`) raises the
error channel `er(lrx)`, and the frame rule extends the state soundly.

---

## 8. Exam-sheet item spanning the four logics

### X.1 (Exam sheet A, Ex. 1) Guard axiom across HL / IL / NC / SIL  `[sheet a + solutions]`
For `⟨| P |⟩ b? ⟨| P ∨ b |⟩` (brackets = a generic triple of HL, IL, NC or SIL),
say for which logics it is sound; prove validity or give a counterexample and the
condition making it sound. Recall `⟦b?⟧P = P ∧ b`.

**Solution.**
- **HL** `{P} b? {P ∨ b}`: valid. `⟦b?⟧P = P∧b ⊆ P∨b`. ✔ Sound.
- **IL** `[P] b? [P ∨ b]`: needs `P∨b ⊆ ⟦b?⟧P = P∧b`. False in general
  (`P=true, b=false ⇒ true ⊆ false`). Sound **iff** `P∨b = P∧b`, i.e. `P = b`.
- **NC** `(P) b? (P ∨ b)`: needs `⟦b?⟧ᵒᵖ(P∨b) ⊆ P`. Since `⟦b?⟧ᵒᵖQ = Q∧b`,
  `⟦b?⟧ᵒᵖ(P∨b) = (P∨b)∧b = b`. Sound **iff** `b ⊆ P`. Counterexample `P=false, b=true`.
- **SIL** `⟨P⟩ b? ⟨P ∨ b⟩`: needs `P ⊆ ⟦b?⟧ᵒᵖ(P∨b) = b`. Sound **iff** `P ⊆ b`.
  Counterexample `P=true, b=false`.
