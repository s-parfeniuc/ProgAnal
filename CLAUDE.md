# Program Analysis — Top-Down Map of the Program Logics (lectures 3–10)

> Intuitive, mostly-natural-language overview of the program logics in the UniPi
> Program Analysis course, with the minimal notation needed. Built as a study
> scaffold for a top-down pass.
>
> **Primary per-logic reference:** [`overviews/`](overviews/README.md) — one full
> explainer + complete LaTeX-math cheatsheet per logic (HL, IL, NC, SIL, SL, ISL, SepSIL).
> This file is the terse cross-cutting map. Atomic notes/pointers in `kb/`
> (see `kb/index.md`); searchable slide text in `lectures-txt/`.
>
> **Metatheory:** every proof from the slides, by macro-topic and tagged by importance,
> in [`proofs/`](proofs/README.md). Exercises in [`exercises/`](exercises/README.md).

---

## 0. The single idea that organizes everything

There is **one semantics** and the logics are its **four viewpoints**, optionally
**lifted to the heap**.

**The semantics.** A command `c` denotes a relation between input and output states.
- **Forward** meaning `⟦c⟧P` = the set of states **reachable** by running `c` from some state in `P` (the *image*).
- **Backward** meaning `⟦c⟧ᵒᵖQ` = the set of states that **can reach** `Q` (the *pre-image* / converse relation). This is exactly Hoare's **weakest possible precondition** `wpp` from lecture 2.

**Two independent choices** give four logics:

| | **Forward** (reason from pre → post) | **Backward** (reason from post → pre) |
|---|---|---|
| **Over-approximation** (`⊆`, "all") | **HL** — Hoare Logic | **NC** — Necessary Conditions |
| **Under-approximation** (`⊇`/`⊆` with "∃") | **IL** — Incorrectness Logic | **SIL** — Sufficient Incorrectness Logic |

- **Over vs under** = *soundness direction*. Over-approx computes a **superset** of the real behaviour → good for proving a bug is **absent** (correctness), but may raise **false alarms**. Under-approx computes a **subset** of genuinely-reachable behaviour → good for proving a bug is **present** (bug-finding), with **no false positives**, but may **miss** bugs.
- **Forward vs backward** = *what you fix and what you compute*. Forward starts from the presumption and pushes reachable states out. Backward starts from the (usually error) postcondition and pulls responsible states in.

**The spatial lift.** Add a **heap** and the **separating conjunction `*`** (+ the **frame rule**) and each forward logic gets a "local reasoning" version that scales:
- **SL** = HL + heap (correctness of pointer programs)
- **ISL** = IL + heap (finding memory bugs)
- **SepSIL** = SIL + heap (finding the *sources* of memory bugs)
(NC + heap is not covered in the course.)

### Master table

| Logic | Triple | Validity | First-order reading | Dir. | Approx. | Proves… |
|---|---|---|---|---|---|---|
| **HL** | `{P} c {Q}` | `⟦c⟧P ⊆ Q` | `∀σ∈P. ∀δ∈⟦c⟧σ. δ∈Q` | fwd | over | absence of bugs (correctness) |
| **IL** | `[P] c [Q]` | `⟦c⟧P ⊇ Q` | `∀δ∈Q. ∃σ∈P. δ∈⟦c⟧σ` | fwd | under | presence of bugs |
| **NC** | `(P) c (Q)` | `⟦c⟧ᵒᵖQ ⊆ P` | `∀δ∈Q. ∀σ∈⟦c⟧ᵒᵖδ. σ∈P` | bwd | over | necessary preconditions |
| **SIL** | `⟨P⟩ c ⟨Q⟩` | `P ⊆ ⟦c⟧ᵒᵖQ` | `∀σ∈P. ∃δ∈Q. δ∈⟦c⟧σ` | bwd | under | source of bugs |
| **SL** | `{P} c {Q}` | `⟦c⟧P ⊆ Q` (heap) | + `*`, frame | fwd | over | correctness of heap programs (local) |
| **ISL** | `[P] c [ε:Q]` | `⟦c⟧ε P ⊇ Q` (heap) | + `*`, frame | fwd | under | memory bugs (local) |
| **SepSIL** | `⟨P⟩ c ⟨Q⟩` | `P ⊆ ⟦c⟧ᵒᵖQ` (heap) | + `*`, frame | bwd | under | sources of memory bugs (local) |

### One rule of thumb for the consequence rule (why they differ)
The `[cons]` direction is fixed by **which side carries the universal-over-a-set**:
- **`∀` over the pre (HL, SIL):** you may **strengthen the pre** (fewer states to worry about) and **weaken the post**.
- **`∀` over the post (IL, NC):** you may **strengthen the post** (fewer states to justify) and **weaken the pre**.

So `{HL, SIL}`: *strengthen pre, weaken post*. `{IL, NC}`: *weaken pre, strengthen post*.
Consequence: an **IL/ISL result cannot be weakened** (only the post — the pre can be weakened); a **SIL precondition cannot be weakened** (only strengthened/shrunk).

### Assignment axioms follow the direction
- **Forward logics (HL, IL, SL, ISL)** use **Floyd's** forward axiom `{P} x:=a {∃x′. P[x′/x] ∧ x=a[x′/x]}`.
- **Backward logics (HL-backward, SIL)** use **Hoare's** substitution axiom `{Q[a/x]} x:=a {Q}`.
- Peculiarity: Hoare's backward axiom is **sound for HL and SIL** but **unsound for IL** (its post could name unreachable states).

---

## 1. Hoare Logic (HL) — *lect. 03–04*

**Core idea / purpose.** The original program logic: prove a program is **correct**
(does the right thing) by annotating it with assertions.

**Triple & meaning.** `{P} c {Q}` means: *starting from any state in `P`, if `c`
terminates, the result is in `Q`* — i.e. `⟦c⟧P ⊆ Q`. This is **partial correctness**
(says nothing about termination). **Total correctness** adds termination via a
**variant** (a well-founded, strictly-decreasing, bounded-below measure).

**Over/under & propagation.** **Forward, over-approximation.** `Q` is a *superset* of
the reachable states. You push a (possibly too-big) set of states forward through the
program. Slogan: *"you may forget information along a path, but must remember all
paths."*

**Inference rules (regular-command form).** One per construct:
`[skip] {P} skip {P}` · `[seq]` compose via a shared middle assertion `R` ·
`[choice]` requires **both** branches reach `Q` · `[while/iter]` needs a **loop
invariant** `{P∧b} c {P} ⟹ {P} while b do c {P∧¬b}` · `[cons]` strengthen pre / weaken
post. Plus auxiliary `disj, conj, frame`.

**Soundness & completeness.** **Sound** (every derivable triple is valid, by induction
on the derivation). **Incomplete in an absolute sense**: "every valid triple is
derivable" fails — `{true} c {false}` is valid iff `c` diverges (halting problem, not
r.e.), and `{true} skip {Q}` valid iff `Q` is a tautology (**Gödel**). But **relatively
complete** (Cook): given an *oracle for logical implications* it is complete, because
`wlp(c,Q)` is expressible and `{wlp(c,Q)} c {Q}` is derivable. The incompleteness is
about arithmetic, not about programs.

**Pros/cons & use.** + The foundation; proves absence of bugs. − Over-approximation ⇒
**false positives** when used for bug-finding; needs human-supplied **invariants**;
undecidable in general. **Use:** program verification.

---

## 2. Incorrectness Logic (IL) — *lect. 05–07* (with `ok`/`er` channels)

**Core idea / purpose.** O'Hearn's (POPL 2020) **dual of HL**: prove the **presence of
bugs** with **no false positives**. "The other side of the coin to Hoare's logic."

**Triple & meaning.** `[P] c [Q]` means `⟦c⟧P ⊇ Q`: *every state in the result `Q` is
genuinely reachable* by running `c` from some state in `P` (`∀δ∈Q. ∃σ∈P. δ∈⟦c⟧σ`). So
if `Q` describes an error and you can derive the triple, the error is **real**.

**Over/under & propagation.** **Forward, under-approximation.** `Q` is a *subset* of the
reachable states — you carry only genuinely-reachable states. Slogan: *"you must
remember information along a path, but may forget some paths."* You can **drop
paths** (rules `[choiceL]/[choiceR]`) and only need a **finite** loop **unrolling**
(no invariant!) because reachability is existential — a finite path is a witness.

**Exit conditions `ok`/`er` (the "real IL", lect. 06).** Triples gain a tag
`[P] c [ε:Q]`, `ε ∈ {ok, er}`: `ok` = normal termination, `er` = **erroneous**
termination (a crash). This is what makes IL *find* bugs:
- `error()` flips everything to the error channel: `[P] error() [ok:false][er:P]`.
- Partial operations produce `er` via a **definedness** predicate, e.g. division:
  `[P] x:=a [er: P ∧ ¬def(a)]` with `def(a₁/a₂)=…∧ a₂≠0`.
- **Propagation = error short-circuiting.** Sequencing:
  `⟦c₁;c₂⟧er = ⟦c₁⟧er ∪ (⟦c₂⟧er ∘ ⟦c₁⟧ok)` — a sequence fails if `c₁` fails (and `c₂`
  never runs) **or** `c₁` succeeds then `c₂` fails. Intuition: **`ok` carries you
  forward along the good prefix to the crash site; `er` collects the reachable crash
  states.** A non-`false` `er` result is a proof of a real, reachable bug.

**Rules.** `[Floyd]` assignment (forward, same as HL). `[cons]` **reversed**
(weaken pre, **strengthen/shrink** post). `[choice]` keeps `Q₁∨Q₂`; `[choiceL/R]` drop
a disjunct. Loops: `[iter0] [P] c⋆ [P]`, `[unroll] [P] c;c⋆ [Q] ⟹ [P] c⋆ [Q]`. **`[conj]`
is unsound.** Bridges to HL: **agreement** and **denial** principles let an IL proof
*refute* an HL spec.

**Soundness & completeness.** **Sound**; **relatively complete** — and its completeness
is *cleaner* than HL's, because assertions are just **sets of states** and implication
is **inclusion**, sidestepping the finiteness/Gödel issues.

**Pros/cons & use.** + No false positives (true-positive theorem); no invariants; fast,
**compositional**. − By design may **miss** bugs; being **forward**, it puts path/error
conditions in the *post*, so it **cannot pinpoint the responsible inputs**; results
cannot be weakened. **Use:** industrial bug-finding (Meta's Infer/Pulse).

---

## 3. Necessary Conditions (NC) — *lect. 07*

**Core idea / purpose.** Infer **necessary preconditions** (Cousot et al., VMCAI 2013):
a condition that, **if violated, guarantees the program is incorrect**. Answers
"under which precondition, if broken, will the program *always* fail?"

**Triple & meaning.** `(P) c (Q)` means `⟦c⟧ᵒᵖQ ⊆ P` (equivalently
`∀δ∈Q. ∀σ∈⟦c⟧ᵒᵖδ. σ∈P`). Reading with `Q` = *good* final states: **every** state that
can reach a good outcome lies in `P`. Contrapositive: `σ∉P ⟹` (ignoring divergence)
every run is bad. So `P` is a **necessary** condition for correctness.

**Over/under & propagation.** **Backward, over-approximation.** You pull back a
*superset* of the states that can reach `Q`.

**Duality with HL (the key fact).** `{P} c {Q} ⟺ (¬P) c (¬Q)` (and `(P) c (Q) ⟺
{¬P} c {¬Q}`). NC is just **HL read in the contrapositive/backward**. HL: given `Q` find
the *weakest* `P` (`wlp`); NC mirrors it: given `Q` find the *strongest* `P`.

**Rules & metatheory.** `[cons]`: weaken pre, strengthen post (same as IL). The course
does **not** give a full standalone proof system — NC is characterized **semantically**
and via the HL duality ("there's not a proof system but…").

**Pros/cons & use.** + Necessary preconditions are easy to explain to users and have an
**extremely low false-positive ratio**; better fit for automatic inference than
sufficient preconditions (which over-burden callers). − It's a correctness-oriented,
over-approximate view; no dedicated proof system here. **Use:** precondition inference
(Microsoft's Clousot/Code Contracts).

---

## 4. Sufficient Incorrectness Logic (SIL) — *lect. 08*

**Core idea / purpose.** Fills the **4th quadrant** (backward + under). Where IL proves
*that* an error is reachable, SIL **reveals the *source* of the error** — which initial
states are **responsible**. (Ascari, Bruni, Gori, Logozzo — OOPSLA 2025.) *SIL is not a
separation logic;* the heap version is SepSIL (§6).

**Triple & meaning.** `⟨P⟩ c ⟨Q⟩` means `P ⊆ ⟦c⟧ᵒᵖQ` (equivalently
`∀σ∈P. ∃δ∈Q. δ∈⟦c⟧σ`): **every** state in `P` has **at least one** execution that
reaches an error in `Q`. So each state of `P` is a **sufficient condition for
incorrectness** — a genuine trigger of the bug.

**Over/under & propagation.** **Backward, under-approximation.** You reason from the
**error postcondition backward**, collecting states each of which *can* cause the error.

**Peculiarities.**
- **Manifest errors** (errors that occur regardless of context) *cannot* be
  characterized by IL, but SIL captures them cleanly: `Q` is a manifest error ⟺
  `⟨true⟩ c ⟨Q⟩` is valid (every initial state reaches the error).
- **IL puts path conditions in the post; SIL puts them in the pre.** e.g. for a bug when
  `even(x)∧odd(y)`: IL derives `[z=11] c [er: z=42 ∧ odd(y) ∧ even(x)]`; SIL derives
  `⟨z=11 ∧ odd(y) ∧ even(x)⟩ c ⟨z=42⟩` (the responsible inputs).
- **HL/SIL coincide for deterministic, terminating `c`:** `⟨P⟩ c ⟨Q⟩ ⟺ {P} c {Q}`.

**Rules.** Backward-oriented, starting from the (error) post. `⟨Hoare⟩` **backward**
assignment `⟨Q[a/x]⟩ x:=a ⟨Q⟩` (the axiom that was *unsound* for IL is *sound* here).
`⟨assume⟩ ⟨Q∧b⟩ b? ⟨Q⟩` (note: the *forward* `⟨P⟩ b? ⟨P∧b⟩` is **invalid** in SIL).
`⟨choice⟩` disjoins the pres. `⟨iter⟩` backward iteration `∀n. ⟨Qₙ₊₁⟩ c ⟨Qₙ⟩ ⟹
⟨∃k.Qₖ⟩ c⋆ ⟨Q₀⟩`. SIL can **drop disjuncts in the pre** (shrink `P`). `⟨conj⟩` is
**unsound**.

**Soundness & completeness.** **Sound and complete** (minimal proof system, complete for
"Lisbon triples"). Completeness is clean for the same set-theoretic reason as IL.

**Pros/cons & use.** + Points programmers at the **root cause** (responsible inputs);
captures manifest errors; sound + complete. − `⟨conj⟩` fails. **Use:** backward
bug-source analysis; foundation for SepSIL.

---

## 5. Separation Logic (SL) — *lect. 09*

**Core idea / purpose.** Extend HL to programs with **pointers and the heap**, enabling
**local reasoning**: *"reasoning and specification confined to the cells a program
actually touches; every other cell automatically stays unchanged"* (Reynolds/O'Hearn/
Yang, CSL 2001). It is still an **over-approximation / correctness** logic.

**State & notation.** A state is `σ = ⟨s, h⟩`: a **store** `s: X→ℤ` (variables→values)
and a **heap** `h: N ⇀ ℤ⊥` (locations→values, partial). Assertions add:
- `a₁ ↦ a₂` — the heap is **exactly one cell** at `a₁` holding `a₂` (ownership).
- `emp` — the empty heap.
- `P₁ * P₂` — **separating conjunction**: the heap **splits into two disjoint parts**,
  one satisfying `P₁`, the other `P₂`. It **splits the heap but not the store**.

Why `*` matters: to say `x`, `y`, `z` point to distinct cells, classical `∧` needs
`x↦1 ∧ y↦2 ∧ z↦3 ∧ (all the ≠ disequations)` — `O(n²)` aliasing conditions. With `*`,
`x↦1 * y↦2 * z↦3` says it **for free** (disjointness is built into `*`).

**The two ingredients: local axioms + frame rule.**
- **Small/local axioms** mention only the cells accessed, giving the strongest post from
  the minimal pre: write `{a↦_} [a]:=v {a↦v}`; read `{a↦v} x:=[a] {x=v ∧ a↦v}`; alloc
  `{emp} x:=alloc() {x↦_}`; dispose `{a↦_} free(a) {emp}`.
- **Frame rule** `{P} c {Q} ⟹ {P*R} c {Q*R}` (side condition: `c`'s modified variables
  are disjoint from `R`'s free variables). `R` is the untouched "frame" — it rides
  through unchanged. This is the `∗`-generalization of the `∧`-frame from IL.

**Over/under & propagation.** **Forward, over-approximation**, but **local**: propagate
the small footprint, frame the rest.

**Soundness & completeness.** **Sound**; but **incomplete** — the **footprint property
fails** because of **information loss**: `free(x)` yields `{emp}`, forgetting that `x`
*held* a location, so you cannot later derive facts like `x≠y`. "Resources can grow but
the model shouldn't let them silently shrink." (This is exactly what ISL fixes.)

**Pros/cons & use.** + **Compositional/scalable** local reasoning for heap-manipulating
code; elegant for data-structure surgery (list reversal/concatenation via inductive
predicates `ls`, `list`). − Incomplete (footprint); still over-approximate ⇒ false
positives if used for bug-finding. **Use:** verification of pointer programs.

---

## 6. Separation Sufficient Incorrectness Logic (SepSIL) — *lect. 10*

**Core idea / purpose.** `SepSIL = SIL + SL`. Backward, under-approximate, **local**
reasoning to reveal the **sources of memory errors** (Ascari, Bruni, Gori, Logozzo —
OOPSLA 2025). Sibling of **ISL** (`= IL + SL`, forward), which we also cover here.

### 6a. ISL (Incorrectness Separation Logic) = IL + SL — *the forward memory-bug logic*
- **Purpose:** local, compositional **bug-catching** for **memory-safety** errors
  (null-dereference, **use-after-free**, double-free). Raad et al., CAV 2020: *"local
  reasoning about the presence of bugs."* **No-false-positives theorem: every reported
  bug is real.**
- **Triple:** `[P] c [ε:Q]` with heap + frame `[P*R] c [ε:Q*R]`. Error axioms, e.g.
  `[x↦v] [x]:=y [ok: x↦y]` but `[x=nil] [x]:=y [er: x=nil]` (null deref).
- **The crucial fix — deallocated cells `x ↦̸`.** The naive frame rule is **unsound**
  in an under-approx setting: from `[x↦v] free(x) [ok: emp]`, framing `x↦v` and using
  `[cons]` "derives" `[false] free(x) [ok: x↦v]`, which is invalid. Cause: SL's `free`
  **shrinks** resources (loses the cell). Fix: `free(x)` yields `[ok: x ↦̸]` (the cell is
  **tracked as deallocated**), giving a **monotonic heap** where *resources never shrink*.
  This makes the frame rule sound **and recovers completeness** (the footprint theorem
  holds). Use-after-free is then `[x↦̸] [x]:=y [er: x↦̸]`, double-free `[x↦̸] free(x) [er: x↦̸]`.
- **Soundness/completeness:** **sound and complete** (footprint), thanks to `↦̸`.
  `[*conj]` is unsound.

### 6b. SepSIL = SIL + SL — *the backward memory-bug-source logic*
- **Triple:** `⟨P⟩ c ⟨Q⟩` with heap + frame `⟨P*R⟩ c ⟨Q*R⟩`. **Backward,
  under-approximation:** every state in `P` is a genuine **source** that can drive `c`
  into the memory error `Q`.
- **Local axioms are Hoare-style/weakest-pre and reuse `↦̸`:** write `⟨x↦_⟩ [x]:=y
  ⟨x↦y⟩`; alloc `⟨emp⟩ x:=alloc() ⟨x↦_⟩`; dispose `⟨x↦_⟩ free(x) ⟨x↦̸⟩`. Because SIL is
  backward, its atomic axioms "speak precisely" and can apply to any post.
- **Vs ISL:** on the same use-after-free example, SepSIL yields a **more succinct
  postcondition** and a **stronger guarantee** — reading *any state in the pre can lead
  to the error* (source characterization) rather than *the error post is reachable*.
- **Soundness/completeness:** **sound and (relatively) complete** — the completeness
  hinges on carefully crafting the assertion language (`↦̸`) and the atomic rules.
- **Use:** automated **backward** reasoning about pointer/heap programs to locate the
  origin of memory errors, with no false positives.

---

## Cheat sheet — how to pick a logic

- **Prove it's correct?** → HL (or SL for heap).
- **Prove a bug is reachable?** → IL (or ISL for memory bugs).
- **Find which inputs are responsible / the root cause?** → SIL (or SepSIL for memory).
- **Infer a precondition whose violation guarantees failure?** → NC.
- **Over-approx** = superset, sound for **absence**, risks **false positives**.
- **Under-approx** = subset, sound for **presence**, **no false positives**, may miss bugs.
- **Forward** = image `⟦c⟧P`, reason pre→post. **Backward** = pre-image `⟦c⟧ᵒᵖQ`, reason post→pre.
- **`*` + frame** = local reasoning; **`↦̸`** = track deallocated cells to keep the heap
  monotonic (needed for sound frame + completeness in the under-approx memory logics).

## Key references (match the course exactly)
- HL: Hoare 1969, *An Axiomatic Basis for Computer Programming*.
- IL: O'Hearn 2020 (POPL), *Incorrectness Logic* — `notes/IL-3371078.pdf`.
- NC: Cousot, Cousot, Fähndrich, Logozzo 2013 (VMCAI), *Automatic Inference of Necessary Preconditions*.
- SIL / SepSIL: Ascari, Bruni, Gori, Logozzo 2025 (OOPSLA), *Revealing Sources of (Memory) Errors via Backward Analysis* — `notes/SIL-3720486.pdf`.
- SL: Reynolds / O'Hearn / Yang 2001–02 (CSL), *Local Reasoning…* — `notes/SL-*.pdf`.
- ISL: Raad, Berdine, Dang, Dreyer, O'Hearn, Villard 2020 (CAV), *Local Reasoning About the Presence of Bugs* — `notes/ISL-*.pdf`.
