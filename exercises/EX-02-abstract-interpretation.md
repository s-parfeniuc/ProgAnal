# Exercises — Abstract Interpretation (Order theory · Galois connections · Abstract domains · Abstract analysis · LCL)

> Exercises from lectures 12–16 plus the matching exam-sheet items. Statements
> first; **Answer / Solution** blocks reproduce what the slides / solution sheet
> give. Source noted as `[lec NN / slide M]`.
> Companion overviews: [`../overviews/08-…`](../overviews/) through `12-local-completeness-logic.md`.

Notation: concrete `(C, ≤)`, abstract `(A, ⊑)`, `γ: A→C`, `α: C→A`; Galois
connection `c ≤ γ(a) ⟺ α(c) ⊑ a`. `BCA` = best correct approximation
`f#(a) = α(f(γ(a)))`; a domain/operation is **complete** when `α∘f = f#∘α`.

---

## 1. Abstract evaluation warm-ups — lect. 12

### AE.1 Sign invariants of the factorial loop  `[lec 12 / slide 32–39]`
Program (computes `k!` for initial `n`):
```
{n > 0}
(1) m := 1;
(2) while n != 0 do {
(3)    m := m * n;
(4)    n := n - 1
(5=2) }
(6) // end
```
Fill in the abstract invariants for `n` and `m` at points (1),(2=5),(3),(4),(6)
under each successively finer sign lattice:
1. lattice `{∅, Z≤0, Z>0, Z}`;
2. lattice adding `Z=0, Z≥0`;
3. lattice adding `Z<0`;
4. start from precondition `true` (i.e. `n : Z`) with the full sign lattice
   `{∅, Z<0, Z=0, Z>0, Z≤0, Z≥0, Z≠0, Z}`.

**Answer (case 4, the richest).**
| pt | n | m |
|----|---|---|
| (1) | Z | Z |
| (2=5) | Z | Z≠0 |
| (3) | Z≠0 | Z>0 |
| (4) | Z≠0 | Z≠0 |
| (6) | Z=0 | Z≠0 |

(Cases 1–3 coarsen these; e.g. case 2 gives `(6): n=Z=0, m=Z>0`.) The program
"computes `k!` or diverges".

### AE.2 Parity abstract operations  `[lec 12 / slide 84–85]`
Domain `A = {∅, ≡₂, ≢₂, Z}` (even/odd). Define the most precise sound
abstractions `+#`, `×#`, `/#` (all commutative).

**Answer.**
```
+#  ∅  ≡₂ ≢₂ Z      ×#  ∅  ≡₂ ≢₂ Z      /#  ∅  ≡₂ ≢₂ Z
∅   ∅  ∅  ∅  ∅       ∅   ∅  ∅  ∅  ∅       ∅   ∅  ∅  ∅  ∅
≡₂  ∅  ≡₂ ≢₂ Z       ≡₂  ∅  ≡₂ ≡₂ ≡₂      ≡₂  ∅  Z  Z  Z
≢₂  ∅  ≢₂ ≡₂ Z       ≢₂  ∅  ≡₂ ≢₂ Z       ≢₂  ∅  Z  Z  Z
Z   ∅  Z  Z  Z       Z   ∅  ≡₂ Z  Z       Z   ∅  Z  Z  Z
```
(Division is very imprecise because integer division of two odds need not be odd.)

### AE.3 Abstract interpretation in the parity domain  `[lec 12 / slide 86–92]`
For the same factorial program, compute the abstract states `S1#…S7#` in
`A = {∅, ≡₂, ≢₂, Z}` where `m := ≢₂` initially, iterating the equations
`S1#=Z×Z, S2#=F2#(S1#), S3#=S2#∪S6#, S4#=F4#(S3#), S5#=F5#(S4#), S6#=F6#(S5#), S7#=F7#(S3#)`.

**Answer (fixpoint).** `S1=Z×Z, S2=≢₂×Z, S3=≢₂×Z, S4=≢₂×Z, S5=Z×Z, S6=Z×Z, S7=≢₂×Z`.

---

## 2. Order theory — lect. 13

### OT.1 Classify 3-element posets  `[lec 13 / slide 41–44]`
For the given 3-element posets (and the labelled poset with elements
`a,b,c,d,e,f,g`): is it a poset? a CPO? a lattice? a complete lattice?

### OT.2 Complete-lattice equivalence  `[lec 13 / slide 45–47]`
For a poset `X`, prove that "∀A⊆X, ⊔A exists" **iff** "∀A⊆X, ⊓A exists".

**Solution.** (⇒) Given `A⊆X`, let `L = {l ∈ X | ∀a∈A. l ⊑ a}` be its lower
bounds. `g = ⊔L` exists by hypothesis; every `a∈A` is an upper bound of `L`, so
`g ⊑ a`, i.e. `g` is itself a lower bound of `A`, and it is the greatest — hence
`g = ⊓A`. (⇐) Dual: `l = ⊓U` of the upper bounds `U` of `A` gives `⊔A`. ∎

### OT.3 Is the divisibility lattice complete?  `[lec 13 / slide 48]`
Is `(N*, |, lcm, gcd)` a complete lattice?

**Answer.** No: chains such as `{2,4,8,16,…}` have no lub, and there is no
greatest element (no glb for `∅`).

---

## 3. Galois connections — the mandatory Ex.1–Ex.12 — lect. 13

> All slides give: two posets `(C,≤)`, `(A,⊑)`, maps `γ:A→C`, `α:C→A` with
> `c ≤ γ(a) ⟺ α(c) ⊑ a`. `[lec 13 / slide 88–121]` — "they are all mandatory!"

### GC.1 Extensivity  `[slide 90–91]`
Prove `γ∘α` is extensive: `∀c. c ≤ γ(α(c))`.
**Solution.** Let `a = α(c)`. From `α(c) ⊑ α(c) = a` and the GC, `α(c) ⊑ a ⟺ c ≤ γ(a) = γ(α(c))`. ∎

### GC.2 Reductivity  `[slide 93–94]`
Prove `α∘γ` is reductive: `∀a. α(γ(a)) ⊑ a`.
**Solution.** Let `c = γ(a)`. From `γ(a) ≤ γ(a)` and the GC, `c ≤ γ(a) ⟺ α(γ(a)) ⊑ a`. ∎

### GC.3 Monotonicity  `[slide 96–97]`
Prove both `γ` and `α` are monotone.
**Solution.** For `c ≤ c₁`: with `a=α(c₁)`, `c ≤ c₁ ≤ γ(α(c₁))` gives `α(c) ⊑ α(c₁)`.
Dually, `a ⊑ a₁` gives `γ(a) ≤ γ(a₁)` using reductivity of `α∘γ`. ∎

### GC.4 Equivalent definition  `[slide 98–99]`
Given monotone `γ, α` with `γ∘α` extensive and `α∘γ` reductive, prove they form
a GC (`c ≤ γ(a) ⟺ α(c) ⊑ a`).
**Solution.** If `c ≤ γ(a)`: `α` monotone + `α∘γ` reductive ⇒ `α(c) ⊑ α(γ(a)) ⊑ a`.
Conversely `α(c) ⊑ a`: `γ` monotone + `γ∘α` extensive ⇒ `c ≤ γ(α(c)) ≤ γ(a)`. ∎

### GC.5 Round-trips  `[slide 102–103]`
Prove `γ∘α∘γ = γ` and `α∘γ∘α = α`.

### GC.6 Idempotency  `[slide 104–105]`
Prove `γ∘α` and `α∘γ` are idempotent. (Immediate from GC.5.)

### GC.7 (α induces γ… / additional)  `[slide 106–107]`
*(Companion property to GC.8; see round-trips.)*

### GC.8 α induces γ  `[slide 108–109]`
Prove `γ(a) = ⋁{ c | α(c) ⊑ a }` for all `a∈A`.
**Solution.** Let `Sₐ = {c | α(c) ⊑ a}`. `γ(a)` is an upper bound (each `c∈Sₐ`
has `α(c)⊑a ⟺ c≤γ(a)`); and `γ(a) ∈ Sₐ` (since `α(γ(a)) ⊑ a`), so it is the
least upper bound. ∎

### GC.9 α preserves lubs  `[slide 112–113]`
Prove `α(⋁D) = ⊔{ α(c) | c∈D }` whenever `⋁D` exists.

### GC.10 γ preserves glbs  `[slide 114–115]`
Prove `γ(⊓B) = ⋀{ γ(a) | a∈B }` whenever `⊓B` exists.

### GC.11 Surjectivity ⟺ Galois insertion  `[slide 118–119]`
Prove `α∘γ = id` iff `α` is surjective.

### GC.12 Injectivity ⟺ Galois insertion  `[slide 120–121]`
Prove `α∘γ = id` iff `γ` is injective.

---

## 4. Abstract domains — lect. 14

### AD.1 Pirahã domain — sound abstractions?  `[lec 14 / slide 27]`
Domain `AP = {⊥, ⊤}` with `γ(⊥)=[0,3]` (values ≤3), `γ(⊤)=[0,∞)`, and
`α(n)=⊥` if `n≤3` else `⊤`. For the three proposed tables of `+#` (and friends),
say for each: is it **sound**? is it the **BCA**?

### AD.2 Pirandello domain — sound abstractions?  `[lec 14 / slide 31]`
Domain `AP = {⊥, 1, ⊤}` with `γ(⊥)={0}, γ(1)={1}, γ(⊤)=[0,∞)`, `α(0)=⊥,
α(1)=1, α(n)=⊤`. For the three proposed `+#` tables: sound? BCA?

### AD.3 Pirandello — BCA of product  `[lec 14 / slide 32]`
Define the BCA `×#` on the Pirandello domain `{⊥, 1, ⊤}`.

### AD.4 Constant domain — sound abstraction of `+`  `[lec 14 / slide 38]`
Constant domain `AZ = {⊥} ∪ ℤ ∪ {⊤}`, `γ(⊤)=Z, γ(n)={n}, γ(⊥)=∅`. Give the BCA
table for `+#` (`⊥` absorbing, `n +# m = n+m`, `⊤` with any non-`⊥` gives `⊤`).

### AD.5 Constant domain — sound abstraction of `×`  `[lec 14 / slide 39]`
Give `×#`. **Then** refine it noting `0` is absorbing: `0 ×# ⊤ = 0`, etc.  `[slide 40]`

### AD.6 Constant domain — adjoint α  `[lec 14 / slide 43–44]`
Define `α: ℘(Z) → AZ` adjoint to `γ`.
**Solution.** `α(∅)=⊥`, `α({n})=n`, `α(X)=⊤` otherwise.

### AD.7 Constant analysis by hand  `[lec 14 / slide 41–42]`
```
X := 0; Y := 10;
while X < 100 do
   Y := Y - 3;
   X := X + Y;     ⟵ ℓ₁: which values for X and Y?
   Y := Y + 3
done
```
Run the non-relational constant analysis (iterate the loop twice) and give the
invariant at `ℓ₁`.
**Answer.** `X = ⊤` (not constant), `Y = 7` — "don't know X, but Y = 7".

### AD.8 Constant-set domain — BCA of product  `[lec 14 / slide 51–52]`
In the bounded-set domain `A|k|` (`γ(⊤)=Z`, `γ(X#)=X#` if `|X#|≤k`), define the
BCA for product.
**Solution.**
```
X# ×# Y# = ∅            if X#=∅ or Y#=∅
         = {0}          else if X#={0} or Y#={0}
         = ⊤            else if X#=⊤ or Y#=⊤
         = ⊤            else if |{x·y | x∈X#, y∈Y#}| > k
         = {x·y | …}    otherwise
```

### AD.9 Constant-set domain — adjoint α  `[lec 14 / slide 53–54]`
Define `α: ℘(Z) → A|2|`.
**Solution.** `α(X) = X` if `|X| ≤ 2`, else `α(X) = ⊤`.

---

## 5. Deriving new domains / abstract analysis — lect. 15

### AA.1 Relational or not?  `[lec 15 / slide 23]`
Classify each domain as relational or non-relational: signs; parity;
intervals-around-0 `[−l, r]`; equalities `c₁x = c₂y`; inequalities `c₁x ≠ c₂y`.
**Answer.** Non-relational: signs, parity, intervals. Relational: equalities,
inequalities.

### AA.2 Completeness 1  `[lec 15 / slide 76]`
Let `P ≜ (x ∈ {−7, 5})` and `c ≜ (x < 0)?; x := −x`.
1. Compute the abstract semantics `⟦c⟧#Sign` on `αSign(P)`.
2. Check whether it equals `αSign(⟦c⟧P)` (i.e. is the analysis complete here?).

### AA.3 Completeness 2  `[lec 15 / slide 77]`
Is the BCA of `f(x) = x if x ≤ 10, else 10` complete on the **Interval** domain?

### AA.4 Completeness 3  `[lec 15 / slide 78]`
For the domain `Sign′ = {⊥, <0, ≥0, ⊤}`:
1. Define `γ` and `α`.
2. Does it admit a **complete** abstract multiplication?

---

## 6. Local Completeness Logic (LCL) — lect. 16

Triples `⊢A [P] c [Q]` parameterised by an abstract domain `A`.

### LCL.1 Which LCL triples are valid (for any `c`, `P`)?  `[lec 16 / slide 53–54]`
- `⊢{⊤} [P] c [false]`
- `⊢{⊤} [P] c [true]`
- `⊢Sign [x > 10] c [false]`
- `⊢{⊤} [wlp(r,P)] c [P]`

### LCL.2 Reasoning: derivation in the Octagon domain  `[lec 16 / slide 55–56]`
Find a derivation for
`⊢Oct [x<10, y>20] if x ≥ y then z := x else z := y [x<10, y>20, z = max(x,y)]`.
**Solution.**
```
[x<10, y>20]
if x ≥ y then
   [false]  z := x  [false]
else
   [x<10, y>20]  z := y  [x<10, z=y>20] ≡ [x<10, y>20, z=max(x,y)]
[x<10, y>20, z = max(x,y)]
```

### LCL.3 Mixed HL+LCL rules — valid?  `[lec 16 / slide 57–58]`
```
   ⊢A [P] c [Q]              ⊢A [P] c [Q]
   ────────────             ─────────────────
   {P} c {A(Q)}             {A(P)} c {A(Q)}
```
**Answer.** Both valid. If `⊢A [P] c [Q]` then `⟦c⟧P ⊆ A(Q)`, so `{P} c {A(Q)}`
holds; and `⟦c⟧A(P) ⊆ ⟦c⟧#A(P) = A(Q)`, so `{A(P)} c {A(Q)}` holds.

### LCL.4 `[conj]` is unsound for LCL  `[lec 16 / slide 59–60]`
**Solution.** `⊢{⊤} [x=0] x:=1 [x=1]` and `⊢{⊤} [x=1] x:=1 [x=1]`; `[conj]`
would give `⊢{⊤} [false] x:=1 [x=1]`, unsound.

### LCL.5 Nondeterministic-assignment rule is unsound  `[lec 16 / slide 61–62]`
Show `⊢A [P] x := nondet() [P[v/x]]` is not sound.
**Solution.** `⊢Id [x=0] x:=nondet() [1=0] ≡ [false]` is unsound: `Id(false)=⊥`
but `Id(⟦x:=nondet()⟧(x=0)) = ⊤`.

---

## 7. Exam-sheet items

### X.2 (Exam sheet A, Ex. 2) GC on `A = {⊥, =0, ≤0, >10, >0, ⊤}`  `[sheet a + solutions]`
Concrete `(℘(Z), ⊆)`.
1. Define `γ: A→℘(Z)` and `α: ℘(Z)→A`.
2. Draw the Hasse diagram of `A`.
3. Define the BCA `·×A·` for integer product.
4. Show `×A` is not complete via a counterexample.

**Solution.**
1. `γ(⊥)=∅, γ(=0)={0}, γ(≤0)={z≤0}, γ(>10)={z>10}, γ(>0)={z>0}, γ(⊤)=Z`.
   `α(X) = ⊥ if X=∅; =0 if X={0}; ≤0 else if X⊆{z≤0}; >10 else if X⊆{z>10};
   >0 else if X⊆{z>0}; ⊤ otherwise`.
2. Hasse diagram:
   ```
              ⊤
           /     \
         ≤0       >0
          |        |
         =0       >10
           \     /
              ⊥
   ```
3. `a ×A b = α({x·y | x∈γ(a), y∈γ(b)})`:
   ```
   ×A    ⊥   =0  ≤0  >10 >0  ⊤
   ⊥     ⊥   ⊥   ⊥   ⊥   ⊥   ⊥
   =0    ⊥   =0  =0  =0  =0  =0
   ≤0    ⊥   =0  ⊤   ≤0  ≤0  ⊤
   >10   ⊥   =0  ≤0  >10 >10 ⊤
   >0    ⊥   =0  ≤0  >10 >0  ⊤
   ⊤     ⊥   =0  ⊤   ⊤   ⊤   ⊤
   ```
4. Take `X = Y = {−1}`. `α(X)=α(Y)=≤0`, but `X×Y = {1}` so `α(X×Y) = >0`.
   Yet `≤0 ×A ≤0 = ⊤` (products of non-positives can be `0` or positive, and the
   domain has no "≥0"). Hence `α(X×Y) = >0 ≠ ⊤ = α(X)×A α(Y)` — not complete. ∎

### X.3 (Exam sheet B, Ex. 2) Powerset lifting is a Galois connection  `[sheet b]`
For `f: Z→Z`, let `Lf(X) ≜ {f(x) | x∈X}` (direct image) and
`If(Y) ≜ {x | f(x)∈Y}` (inverse image) on `(℘(Z), ⊆)`.
1. Prove `Lf` and `If` form a Galois connection.
2. Under which condition on `f` do they form a Galois **insertion**?

**Answer (guide).** `Lf(X) ⊆ Y ⟺ X ⊆ If(Y)`, so `(Lf, If)` is a GC with `Lf`
the lower adjoint. It is an insertion (`Lf∘If = id`) iff `f` is **surjective**.
