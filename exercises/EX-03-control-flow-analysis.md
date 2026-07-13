# Exercises — Control Flow Analysis (0-CFA / k-CFA for FUN · CFA for the π-calculus)

> Exercises from the CFA lectures (18–23, plus the `CFA-for-FUN` / `CFA-for-Pi`
> decks) and the matching exam-sheet items. Statements first; **Answer /
> Solution** blocks reproduce what the slides / solution sheet give.
> Source noted as `[lec NN / slide M]`.
> Companion overviews: [`../overviews/13-…`](../overviews/) through `19-cfa-pi-applications.md`.

Notation: `(Ĉ, ρ̂) ⊨ e` = the abstract cache `Ĉ: Lab→℘(Term)` and environment
`ρ̂: Var→℘(Term)` are an **acceptable** 0-CFA result for the labelled expression
`e`. `⊨s` = syntax-directed variant. `fn x => e0` denotes an abstract closure.

---

## 1. 0-CFA for FUN — label, guess, verify — lect. 18 / CFA-for-FUN

> `[CFA-for-FUN / slide 67–76]` (mirrored in `[lec 18 / slide 2–11]`).
> For each expression: add labels to all subexpressions, guess an acceptable
> `(Ĉ, ρ̂)`, and verify it against the acceptability relation `⊨`.

### CFA.1 Exercise 1  `[slide 69–71]`
`e ≜ ((fn x => (x¹ + 12²)³)⁴ (3)⁵)⁶`

**Solution.**
```
Ĉ(1) = ∅           Ĉ(4) = {fn x => (x¹+12²)³}     ρ̂(x) = ∅ (i.e. {3})
Ĉ(2) = ∅           Ĉ(5) = ∅ (i.e. {3})
Ĉ(3) = ∅           Ĉ(6) = ∅ (i.e. {3})
```
Verification unfolds `⊨` down to:
`{fn x => (x¹+12²)³} ⊆ Ĉ(4)`, `Ĉ(5) ⊆ ρ̂(x)`, `Ĉ(3) ⊆ Ĉ(6)`, `ρ̂(x) ⊆ Ĉ(1)`,
all `✔`.

### CFA.2 Exercise 2  `[slide 72–75]`
`e ≜ ((fn f => ((f¹ 76²)³ + (f⁴ 77⁵)⁶)⁷)⁸ (fn a => a⁹)¹⁰)¹²`

**Solution (acceptable result).**
```
Ĉ(1)  = {fn a => a⁹}                 Ĉ(8)  = {fn f => ((f¹76²)³+(f⁴77⁵)⁶)⁷}
Ĉ(4)  = {fn a => a⁹}                 Ĉ(12) = {fn f => ((f¹76²)³+(f⁴77⁵)⁶)⁷}
Ĉ(10) = {fn a => a⁹}                 Ĉ(2)=Ĉ(3)=Ĉ(5)=Ĉ(6)=Ĉ(7)=Ĉ(9)=Ĉ(11)=∅
ρ̂(f) = {fn a => a⁹}                  ρ̂(a) = ∅
```
Key constraints checked: `Ĉ(10) ⊆ ρ̂(f)`, `Ĉ(2),Ĉ(5) ⊆ ρ̂(a)`,
`Ĉ(9) ⊆ Ĉ(3), Ĉ(6)`, `Ĉ(8) ⊆ Ĉ(12)`.

### CFA.3 Exercise 3  `[slide 76]`  *(complete it yourself)*
```
let f = fn x => x  in
let g = fn y => y + 2  in
let h = fn z => z + 3  in
(f g) + (f h)
```
Labelled form (`idw ≜ fn w => wˡ`):
`e ≜ (let f = (fn x => (x¹)²)³·⁴ in (let g = (fn y => (y⁵+2⁶)⁷)⁸ in (let h = (fn z => (z⁹+3¹⁰)¹¹)¹² in ((f¹³ g¹⁴)¹⁵ + (f¹⁶ h¹⁷)¹⁸)¹⁹)²⁰)²¹)²²`.
Guess an acceptable `(Ĉ, ρ̂)` and verify it. (Note: like the exam sheet A Ex. 3,
`ρ̂(x)` must merge the closures of `g` and `h` — 0-CFA loses precision across the
two calls of `f`.)

---

## 2. Metatheory of syntax-directed CFA — lect. 19 / CFA-for-FUN

### CFA.4 Uniqueness of the syntax-directed solution  `[lec 19 / slide 26], [CFA-for-FUN / slide 126]`
Let `⊨s'` and `⊨s''` be two relations satisfying the **syntax-directed** CFA
clauses. Show, by structural induction on `e`, that `(Ĉ,ρ̂) ⊨s' e ⟺ (Ĉ,ρ̂) ⊨s'' e`.

**Solution sketch.** `[cˡ]` trivial. `[xˡ]` both reduce to `ρ̂(x) ⊆ Ĉ(l)`.
`[(fn x => t₀ˡ⁰)ˡ]` both require `{fn x=>e₀} ⊆ Ĉ(l) ∧ (Ĉ,ρ̂) ⊨s t₀ˡ⁰`, and the
premise on the body is equivalent by the IH. Remaining cases analogous. Since the
clauses fully determine the relation, there is exactly one syntax-directed solution.

### CFA.5 The non-syntax-directed relation is *not* unique  `[lec 19 / slide 27]`  *(observation on CFA.4)*
Show that two relations satisfying the **non**-syntax-directed clauses can differ.
**Answer.** For `a ≜ (0¹ 0²)³` with `(fn x => a⁴) ∈ Ĉ(1)` and `Ĉ(2)=ρ̂(x)=∅`, the
clause for `a³` requires `(Ĉ,ρ̂) ⊨' a⁴`, but whether `a` itself is *in* the
relation is unconstrained — so both an including and a non-including relation
satisfy the clauses. (The function `Ĉ(1)` introduces a dependency outside the
syntactic structure.)

### CFA.6 CBV order — guard the operand  `[lec 19 / slide 36–38], [CFA-for-FUN / slide 136]`
Modify the original CFA `[app]` clause to reflect left-to-right call-by-value
order: **do not analyse the operand** if the operator cannot produce any closure.
Then exhibit a program the modified analysis accepts but the original rejects.

**Solution.** New clause:
```
[app] (Ĉ,ρ̂) ⊨ (t₁ˡ¹ t₂ˡ²)ˡ  iff  (Ĉ,ρ̂) ⊨ t₁ˡ¹ ∧
   ( (Ĉ(l₁) ∩ Val̂) ≠ ∅  ⇒  (Ĉ,ρ̂) ⊨ t₂ˡ² ) ∧
   ( ∀(fn x => t₀ˡ⁰) ∈ Ĉ(l₁) : (Ĉ,ρ̂) ⊨ t₀ˡ⁰ ∧ Ĉ(l₂) ⊆ ρ̂(x) ∧ Ĉ(l₀) ⊆ Ĉ(l) )
```
Example: `e ≜ 4 (fn y => y)` — the operator `4` is not a closure, so the empty
analysis is acceptable for the modified analysis but **not** for the original one.

### CFA.7 Reachability-tracking CFA  `[lec 19 / slide 39–40]`  *(design exercise)*
The syntax-directed analysis analyses every subexpression "exactly once", adding
constraints even from unreachable code. Amend it so that (i) only reachable
subexpressions are analysed and (ii) each is analysed "at most once".
**Answer sketch.** Add a reachability component `R̂ ∈ Reach: Lab → ℘({on})`;
`{on} ⊆ R̂(l)` means "label `l` is reachable". A function body `t₀ˡ⁰` is analysed
(`(Ĉ,ρ̂,R̂) ⊨s' t₀ˡ⁰`) iff `{on} ⊆ R̂(l₀)`, i.e. iff the function is actually
applied somewhere — so bodies are analysed at most once.

---

## 3. CFA for the π-calculus — CFA-for-Pi / lect. 23

### CFA.8 The `match` clause  `[CFA-for-Pi / slide 41], [lec 23 / slide 27]`
Propose a CFA clause for name matching `[x = y]P` that only analyses the
continuation when the match can succeed.
**Solution.**
```
[match] (ρ, κ) ⊨P [x = y]P   iff   ( ρ(x) ∩ ρ(y) ≠ ∅  ⇒  (ρ, κ) ⊨P P )
```
Example: `a(x).c(y).[x=y].P′ | ā⟨d⟩.Q′ | ā⟨b⟩.Q″ | c̄⟨b⟩.R′` gives
`ρ(x)={b,d}, ρ(y)={b}`, so `ρ(x)∩ρ(y)={b}` and `P′` is analysed; but with
`c̄⟨f⟩` instead, `ρ(y)={f}` and `ρ(x)∩ρ(y)=∅`, so `P′` is skipped.

### CFA.9 Imprecision of 0-CFA on π  `[CFA-for-Pi / slide 44], [lec 23 / slide 30]`  *(discussion)*
For `P₁ ≜ a(x) | ā⟨b⟩`, `P₂ ≜ a(x) + ā⟨b⟩`, `P₃ ≜ a(x) . ā⟨b⟩`, explain why the
0-CFA (context-insensitive) estimate has `ρ(x) ⊇ {b}` in all three cases even
though only in `P₁` can the input actually be bound to `b`.

---

## 4. Exam-sheet items

### X.3a (Exam sheet A, Ex. 3) 0-CFA and 1-CFA of `apply`  `[sheet a + solutions]`
```
let apply = fn f => f 2
 in let inc = fn x => x + 4
     in let dbl = fn y => y * 2
         in (apply inc) - (apply dbl)
```
1. Label all subexpressions and abstractions.
2. Guess a Pure 0-CFA result and verify it with `⊨`; comment on the abstract
   values at the two calls to `apply`.
3. Add the extra flow `fn w => w ∈ Ĉ(Label(f))`. Does `⊨` still hold? What does
   this say about soundness vs precision?
4. How does the syntax-directed `⊨s` change the analysis?
5. Extract the corresponding constraint system.
6. How does the result change under 1-CFA? Which spurious flows disappear, and why?

**Solution (condensed).**
1. Labelling:
   `e ≜ (let apply = (fn f => (f¹ 2²)³)⁴ in (let inc = (fn x => (x⁵+4⁶)⁷)⁸ in
   (let dbl = (fn y => (y⁹*2¹⁰)¹¹)¹² in ((apply¹³ inc¹⁴)¹⁵ − (apply¹⁶ dbl¹⁷)¹⁸)¹⁹)²⁰)²¹)²²`
2. Acceptable 0-CFA:
   ```
   Ĉ(4)  = {fn f => (f¹2²)³}          ρ̂(apply) = {fn f => (f¹2²)³}
   Ĉ(8)  = {fn x => (x⁵+4⁶)⁷}         ρ̂(inc)   = {fn x => (x⁵+4⁶)⁷}
   Ĉ(12) = {fn y => (y⁹*2¹⁰)¹¹}       ρ̂(dbl)   = {fn y => (y⁹*2¹⁰)¹¹}
   Ĉ(13) = Ĉ(16) = {fn f => (f¹2²)³}
   Ĉ(14) = {fn x => …⁷}   Ĉ(17) = {fn y => …¹¹}
   Ĉ(1)  = {fn x => …⁷, fn y => …¹¹}  ρ̂(f) = {fn x => …⁷, fn y => …¹¹}
   Ĉ(i)  = ∅ for the remaining labels
   ```
   Key point: `Ĉ(14) ⊆ ρ̂(f)` **and** `Ĉ(17) ⊆ ρ̂(f)` — 0-CFA merges the two
   calling contexts of `apply` into the single variable `f`, losing precision.
3. Adding `fn w => w ∈ Ĉ(1)`: `⊨` may still hold (it only *adds* flow), so it
   stays **sound** — but **less precise**, since `fn w => w` never really flows to
   `f`. Acceptability expresses soundness, not optimal precision.
4. `⊨s` analyses each function body **once at definition time** (not per
   application): no re-analysis on multiple calls, but bodies of never-applied
   functions are still analysed.
5. Constraint system (excerpt): `{fn f=>(f¹2²)³} ⊆ Ĉ(4)`, `Ĉ(4) ⊆ ρ̂(apply)`,
   `{fn x=>(x⁵+4⁶)⁷} ⊆ Ĉ(8)`, `Ĉ(8) ⊆ ρ̂(inc)`, `{fn y=>(y⁹*2¹⁰)¹¹} ⊆ Ĉ(12)`,
   `Ĉ(12) ⊆ ρ̂(dbl)`, `Ĉ(15),Ĉ(18) ⊆ Ĉ(19) ⊆ Ĉ(20) ⊆ Ĉ(21) ⊆ Ĉ(22)`; plus
   the conditional application constraints
   `{fn f=>…} ⊆ Ĉ(13) ⇒ Ĉ(14) ⊆ ρ̂(f) ∧ Ĉ(3) ⊆ Ĉ(15)` (and symmetrically for 16/18),
   and inside the body `{fn x=>…⁷} ⊆ Ĉ(1) ⇒ Ĉ(2) ⊆ ρ̂(x) ∧ Ĉ(7) ⊆ Ĉ(3)`,
   `{fn y=>…¹¹} ⊆ Ĉ(1) ⇒ Ĉ(2) ⊆ ρ̂(y) ∧ Ĉ(11) ⊆ Ĉ(3)`.
6. Under **1-CFA** the two calls get distinct call strings `δ₁=⟨15⟩`, `δ₂=⟨18⟩`:
   `ρ̂(f,15) = {fn x=>…⁷}`, `ρ̂(f,18) = {fn y=>…¹¹}`, hence
   `Ĉ(1,15) = {inc-closure}`, `Ĉ(1,18) = {dbl-closure}`. The spurious flows
   disappear (`dbl ∉ Ĉ(1,15)`, `inc ∉ Ĉ(1,18)`): `Ĉ(15)` holds only the result
   of `inc`, `Ĉ(18)` only that of `dbl`. 1-CFA separates the calls by call site.

### X.3b (Exam sheet B, Ex. 3) 0-CFA + DFA sign analysis of `choose`  `[sheet b]`
```
let n = 5
 in let choose = if n > 0 then (fn x => x + 1) else (fn y => y * 2)
   in choose 4
```
Sign analysis with `Data_sign = {tt, ff, −, 0, +}`.
1. Label all subexpressions and abstractions.
2. Guess a Pure 0-CFA result and verify it with `⊨`; determine the closures
   flowing to `choose` at the application `(choose 4)`.
3. Explain why Pure 0-CFA cannot see that one branch of the conditional is
   unreachable.
4. Perform the DFA with abstract values as powersets `V̂al_d = ℘(Data_sign)`;
   compute the abstract values of `5`, `n`, `n > 0`, `4`.
5. Explain how the DFA refines the CFA result. Which branch becomes unreachable?
6. Repeat the DFA using the complete-lattice formulation of the same sign
   information and compare the two analyses.
7. Explain why the refined CFA+DFA result is still sound.

*(Exam sheet B has no published solution; work it through using CFA.6/CFA.7 —
guarded operand analysis and reachability — as the model. Both branch closures
flow to `choose` under pure 0-CFA; the DFA determines `n > 0 = tt`, killing the
`else` branch so only `fn x => x + 1` reaches `(choose 4)`.)*
