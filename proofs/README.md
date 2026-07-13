# Proofs — index

Every **theorem, lemma, soundness/completeness result and counterexample proved on the
lecture slides** (lectures 02–23, `CFA-for-FUN`, `CFA-for-Pi`), extracted and grouped into
the same three macro-topics as [`../exercises/`](../exercises/README.md). Each entry gives
the statement, the proof as the slides present it, its source `[lec NN / slide M]`, and an
**importance tag**.

| File | Macro-topic | Covers | Source lectures |
|---|---|---|---|
| [PR-01-program-logics.md](PR-01-program-logics.md) | **Program logics** | HL soundness/(in)completeness, IL soundness/completeness + agreement/denial, HL↔NC duality, SIL, SL incompleteness, ISL frame fix, SepSIL | 03–10 |
| [PR-02-abstract-interpretation.md](PR-02-abstract-interpretation.md) | **Abstract interpretation** | sound/best/complete abstractions, the 12 Galois-connection proofs, fixpoint transfer, widening, LCL metatheory | 11–16 |
| [PR-03-control-flow-analysis.md](PR-03-control-flow-analysis.md) | **Control flow analysis** | subject reduction, Moore families & least solutions, syntax-directed and constraint-based preservation, algorithm correctness, complexity, CFA for π | 17–23, CFA-for-FUN, CFA-for-Pi |

## Importance tags

Assigned by **how much lecture time the slides spend on the result** — number of slides
devoted to it, whether the proof is carried out in full or deferred to the paper, and whether
it is re-used later in the course.

| Tag | Meaning |
|---|---|
| **★★★** | Core. Proved in full on the slides, usually over several slides, and re-used. The results the course is *built on* (HL/IL soundness & completeness, HL↔NC duality, the Galois-connection toolkit, fixpoint transfer, LCL verification theorem, subject reduction, Moore families). Expect these on the exam. |
| **★★** | Secondary. Proved or sketched on one or two slides; important but supporting (agreement/denial, BCA composition, complete-guard conditions, k-CFA complexity, π adequacy results). |
| **★** | Minor. Stated with the proof deferred to the paper, or a one-line observation/witness (SIL soundness & completeness, LCL intrinsic incompleteness, trivially-valid triples, satisfaction witnesses). |

## Relation to the other folders

- **Statement vs proof.** Many slide "proofs" are posed as exercises; those appear in both
  places. [`../exercises/`](../exercises/README.md) gives the *question* (cover the answer and
  try cold); this folder gives the *proved result* organized by theorem, so you can revise the
  metatheory as a block. Cross-references are given inline.
- **Narrative.** [`../overviews/`](../overviews/README.md) is the per-logic/per-topic
  explainer with the full LaTeX cheatsheets; [`../CLAUDE.md`](../CLAUDE.md) is the top-down map.
- **Sources.** Searchable slide text in [`../lectures-txt/`](../lectures-txt/), original PDFs in
  [`../lectures/`](../lectures/), papers in [`../notes/`](../notes/).

## The ★★★ list (revise these first)

**Program logics** — HL soundness (induction on the derivation; the `seq`/`while` cases) ·
Floyd's axiom soundness · HL incompleteness I (halting) & II (Gödel) · relative completeness
(Cook, via `wlp`) · IL soundness · IL relative completeness (incl. the Kleene-star case) ·
Hoare's backward axiom is unsound for IL · `[conj]` unsound · HL↔NC duality
`{P}c{Q} ⟺ (¬P)c(¬Q)` · manifest errors ⟺ `⟨true⟩c⟨Q⟩` · `⟨conj⟩` and the forward `assume`
unsound in SIL · footprint fails in SL (information loss) · the unsound ISL frame rule and its
`↦̸` fix · `[∗conj]` unsound.

**Abstract interpretation** — the three equivalent soundness formulations · the BCA is the
least sound abstraction · GC.P1–P12 (all twelve, "they are all mandatory") · Sign `×` complete
/ `+` only correct · fixpoint transfer (sound ⟹ over-approx; complete ⟹ exact) ·
complete-guard characterization · LCL convexity lemma · LCL logical correctness and the
verification theorem.

**Control flow analysis** — subject reduction for 0-CFA (all five cases + the Fact) ·
acceptable analyses form a Moore family (least solution exists) · `⊧s ⟹ ⊧` (and the converse
counterexample) · Moore family for `⊧s` · correctness/termination/minimality of the worklist
algorithm · congruence + substitution + subject reduction for the π-calculus.
