---
title: Program Analysis — Knowledge Base
type: index
course: "Program Analysis 2025–26 (0078A, 6 CFU) — Università di Pisa"
teachers: [Chiara Bodei, Roberto Bruni, Roberta Gori]
---

# Program Analysis — Map of Content

Knowledge base for the Program Analysis course (UniPi). Each note links to its
source PDF (lecture deck and/or reading in `notes/`) and to related concepts.
Links use `[[wikilink]]` syntax (Obsidian / Foam VSCode extension).

> [!info] Status legend
> ✅ full note · 🟡 stub (fill in when you reach the lecture) · ❓ topic label to confirm against the deck

## How to use
- Open this vault folder in **Obsidian**, or install the **Foam** extension in VSCode, to get backlinks + graph view.
- Every note carries a `source:` field pointing at the lecture/reading it came from.
- Add new atomic notes and link them; the [[glossary]] collects symbols and short definitions.
- **Search the lectures:** `lectures-txt/` holds an auto-extracted text layer of all 27 decks (per-slide markers, `⟦ ⟧`→`[[ ]]`). `grep -rin "wpp" lectures-txt/` etc. ⚠️ Text layer only — may reorder lines / drop ligatures / rasterize some math; for exact math read the slide image. Regenerate with `scratchpad/extract.py`.

---

## 0. Foundations
- [[glossary]] — symbols, operators, one-line definitions ✅
- [[denotational-semantics]] — meaning as `⟦·⟧`; states/`Σ`, concrete domain `℘(Σ)`, assertion language, partial correctness, `wlp`/`wpp` (∀ vs ∃), backward semantics, exact vs approx ✅ · *lect. 02*

## 1–3. Program logics (HL · IL · NC · SIL · SL · ISL · SepSIL)
> **Consolidated in [`../overviews/`](../overviews/README.md)** — the **primary reference**
> (one full explainer + complete cheatsheet per logic, LaTeX-math, the taxonomy map). The
> kb notes below are pointers kept so existing `[[wikilinks]]` resolve.

- [[hoare-logic]] · [[total-correctness]] → **[overviews/01 HL](../overviews/01-hoare-logic.md)** — `{P} c {Q}`, `⟦c⟧P ⊆ Q` (fwd · over) · *lect. 03–04*
- [[incorrectness-logic]] · [[real-incorrectness-logic]] → **[overviews/02 IL](../overviews/02-incorrectness-logic.md)** — `[P] c [ε:Q]`, `⟦c⟧P ⊇ Q` (fwd · under) · *lect. 05–07*
- [[il-nc]] → **[overviews/03 NC](../overviews/03-necessary-conditions.md)** — `(P) c (Q)`, `⟦c⟧ᵒᵖQ ⊆ P` (bwd · over) · *lect. 07*
- **SIL** → **[overviews/04 SIL](../overviews/04-sufficient-incorrectness-logic.md)** — Sufficient IL, `⟨P⟩ c ⟨Q⟩`, `P ⊆ ⟦c⟧ᵒᵖQ` (bwd · under) · *lect. 08*
- [[separation-logic]] → **[overviews/05 SL](../overviews/05-separation-logic.md)** — HL+heap, `∗` + frame (fwd · over · local) · *lect. 09*
- [[incorrectness-separation-logic]] → **[overviews/06 ISL](../overviews/06-incorrectness-separation-logic.md)** — IL+heap, `↦̸` (fwd · under · local) · *lect. 10*
- **SepSIL** → **[overviews/07 SepSIL](../overviews/07-separation-sufficient-incorrectness-logic.md)** — SIL+heap (bwd · under · local) · *lect. 10*

## 4. Abstract Interpretation (lect. 11–15) → consolidated in [`../overviews/`](../overviews/README.md) Part II
- [[intro-abstract-interpretation]] → **[overviews/08](../overviews/08-intro-abstract-interpretation.md)** — the idea, over-approximation, soundness vs precision, domains · *lect. 11–12*
- [[galois-connections]] → **[overviews/09](../overviews/09-order-theory-galois-connections.md)** — posets/lattices/ACC, `α ⊣ γ`, Galois insertion, closures · *lect. 13*
- [[abstract-domains]] → **[overviews/10](../overviews/10-abstract-domains-operators.md)** — transfer functions, BCA `f♯=α∘F∘γ`, completeness, products · *lect. 12/14/15*
- [[abstract-analysis]] → **[overviews/11](../overviews/11-abstract-analysis-fixpoints-widening.md)** — analysis as fixpoint, fixpoint transfer, widening/narrowing · *lect. 12/15*
- [[local-completeness-logic]] — LCL: correctness **and** incorrectness via AI 🟡 · *lect. 16* (not yet done)

## 5. Control Flow Analysis (CFA)
- [[control-flow-analysis]] — 0-CFA, flow logic, acceptability judgements 🟡 · *lect. 17–23*
- [[cfa-for-fun]] — CFA for the functional language FUN 🟡
- [[cfa-for-pi]] — CFA for the π-calculus 🟡

---

## Readings (`notes/`)
| Topic | File |
|---|---|
| Hoare Logic | `notes/HL-Winskel-Ch6-7.pdf` |
| Incorrectness Logic | `notes/IL-3371078.pdf` |
| Separation Logic | `notes/SL-3-540-44802-0_1.pdf` |
| Incorrectness Sep. Logic | `notes/ISL-978-3-030-53291-8_14.pdf` |
| LCL | `notes/LCL - A Correctness and Incorrectness Program Logic - 3582267.pdf` |
| Abstract Interpretation | `notes/Abstract Interpretation - Tutorial by Mine.pdf`, `notes/Abstract Interpretation - Notes by Ranzato.pdf`, `notes/Cousot - Principles of abstract interpretation - Ch8-11.pdf` |
| Static analysis intro | `notes/Rival - Introduction to Static Analysis - Ch1-2.pdf` |

## Exercises
- `exercises/ProgramAnalysis_exercises_a.pdf` (+ `_a_solutions.pdf`)
- `exercises/ProgramAnalysis_exercises_b.pdf`
