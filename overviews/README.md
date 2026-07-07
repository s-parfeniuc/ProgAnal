---
title: Program Analysis — Overviews
type: index
---

# Program Analysis — Overviews

One self-contained file per topic: a mostly natural-language explanation (purpose,
definition, over/under-approximation & propagation, peculiarities, soundness &
completeness with *why*, pros/cons, use cases) followed by a **complete formal
cheatsheet** (definitions, semantics, every axiom/rule/theorem).

These `overviews/` files are the **primary reference**. The terse cross-cutting map lives
in [`../CLAUDE.md`](../CLAUDE.md); atomic notes/pointers in `../kb/`.

## Part I — Program logics (lect. 03–10)
1. [Hoare Logic (HL)](01-hoare-logic.md) — *lect. 03–04* — forward, over-approx — correctness
2. [Incorrectness Logic (IL)](02-incorrectness-logic.md) — *lect. 05–07* — forward, under-approx — bug presence (incl. `ok`/`er`)
3. [Necessary Conditions (NC)](03-necessary-conditions.md) — *lect. 07* — backward, over-approx — necessary preconditions
4. [Sufficient Incorrectness Logic (SIL)](04-sufficient-incorrectness-logic.md) — *lect. 08* — backward, under-approx — bug sources
5. [Separation Logic (SL)](05-separation-logic.md) — *lect. 09* — forward, over-approx, **heap/local** — heap correctness
6. [Incorrectness Separation Logic (ISL)](06-incorrectness-separation-logic.md) — *lect. 10* — forward, under-approx, **heap/local** — memory bugs
7. [Separation Sufficient Incorrectness Logic (SepSIL)](07-separation-sufficient-incorrectness-logic.md) — *lect. 10* — backward, under-approx, **heap/local** — memory-bug sources

## Part II — Abstract Interpretation (lect. 11–15)
8. [Introduction to Abstract Interpretation](08-intro-abstract-interpretation.md) — *lect. 11–12* — the idea, over-approximation, soundness vs precision, the numeric domains
9. [Order Theory & Galois Connections](09-order-theory-galois-connections.md) — *lect. 13* — posets/lattices/ACC, `α ⊣ γ`, Galois insertion, closures
10. [Abstract Domains & Operators](10-abstract-domains-operators.md) — *lect. 12/14/15* — transfer functions, **BCA** `f♯ = α∘F∘γ`, completeness, products
11. [Abstract Analysis — Fixpoints, Widening & Narrowing](11-abstract-analysis-fixpoints-widening.md) — *lect. 12/15* — analysis as fixpoint, fixpoint transfer, `∇` / `△`

> **Bridge:** AI is the **over-approximation** framework (sound for proving *absence* of
> bugs, like HL/SL), made computable via abstract domains and fixpoints. Its dual under-approx
> siblings are the incorrectness logics (Part I).

## Bridge — correctness ⟷ incorrectness (lect. 16)
12. [Local Completeness Logic (LCL)](12-local-completeness-logic.md) — *lect. 16* — combines over- (AI) and under- (IL) approximation: prove a program **correct** *or* produce a **genuine bug**, when the abstraction is *locally* complete along the run.

## Part III — Control Flow Analysis (lect. 17–23)
*Strand A — CFA for the functional language FUN:*
13. [CFA: Motivation & the 0-CFA Specification](13-cfa-motivation-0cfa-specification.md) — *lect. 17* — dynamic dispatch, FUN + labelling, abstract cache `Ĉ`/env `ρ̂`, the acceptability relation `(Ĉ,ρ̂) ⊧ e` + clauses
14. [0-CFA: Semantic Correctness](14-0cfa-semantic-correctness.md) — *lect. 18* — SOS with closures, **subject reduction**
15. [0-CFA: Existence & the Least Solution](15-0cfa-existence-least-solutions.md) — *lect. 19* — Moore family, coinduction, syntax-directed `⊧ₛ`
16. [0-CFA: Constraint-Based Formulation & Solving](16-0cfa-constraint-based-solving.md) — *lect. 20* — (conditional) constraints, worklist solver, `O(n³)`
17. [Beyond 0-CFA: Abstract Values & Context Sensitivity](17-beyond-0cfa-abstract-values-context.md) — *lect. 21–22* — CFA+DFA (constant propagation), **k-CFA**, Cartesian Product Algorithm

*Strand B — CFA for the concurrent π-calculus:*
18. [CFA for the π-calculus — the Calculus & 0-CFA](18-cfa-pi-calculus.md) — *lect. 22–23* — π-calculus, mobility, reduction; 0-CFA `(ρ̂,κ̂)` predicting communications
19. [CFA for the π-calculus — Applications](19-cfa-pi-applications.md) — *lect. 23* — well-sortedness, **security** (secrecy, non-leaking), **taint**, CFA vs type systems

## Part I — the organizing picture

One semantics, two axes. **Forward** uses the image $\llbracket c\rrbracket P$ (states
reachable from $P$); **backward** uses the pre-image $\llbracket c\rrbracket^{op}Q$ (states
that can reach $Q$; $=$ Hoare's *weakest possible precondition* $wpp$). **Over**
($\subseteq$, "$\forall$") is sound for proving **absence** of bugs but risks false
positives; **under** ($\supseteq$ / $\subseteq$-with-"$\exists$") is sound for proving
**presence** of bugs with no false positives but may miss bugs.

| | **Forward** (image $\llbracket c\rrbracket P$) | **Backward** (pre-image $\llbracket c\rrbracket^{op}Q$) |
|---|---|---|
| **Over-approx** ($\subseteq$) | **HL** $\;\llbracket c\rrbracket P \subseteq Q$ | **NC** $\;\llbracket c\rrbracket^{op}Q \subseteq P$ |
| **Under-approx** ($\supseteq$) | **IL** $\;\llbracket c\rrbracket P \supseteq Q$ | **SIL** $\;P \subseteq \llbracket c\rrbracket^{op}Q$ |

**Spatial lift** (add heap, separating conjunction $\ast$, frame rule → *local reasoning*):
SL $=$ HL$+$heap, ISL $=$ IL$+$heap, SepSIL $=$ SIL$+$heap.

| Logic | Triple | Validity | First-order reading | Dir. | Approx. |
|---|---|---|---|---|---|
| HL | $\{P\}\,c\,\{Q\}$ | $\llbracket c\rrbracket P \subseteq Q$ | $\forall\sigma{\in}P.\,\forall\delta{\in}\llbracket c\rrbracket\sigma.\,\delta{\in}Q$ | fwd | over |
| IL | $[P]\,c\,[Q]$ | $\llbracket c\rrbracket P \supseteq Q$ | $\forall\delta{\in}Q.\,\exists\sigma{\in}P.\,\delta{\in}\llbracket c\rrbracket\sigma$ | fwd | under |
| NC | $(P)\,c\,(Q)$ | $\llbracket c\rrbracket^{op}Q \subseteq P$ | $\forall\delta{\in}Q.\,\forall\sigma{\in}\llbracket c\rrbracket^{op}\delta.\,\sigma{\in}P$ | bwd | over |
| SIL | $\langle P\rangle\,c\,\langle Q\rangle$ | $P \subseteq \llbracket c\rrbracket^{op}Q$ | $\forall\sigma{\in}P.\,\exists\delta{\in}Q.\,\delta{\in}\llbracket c\rrbracket\sigma$ | bwd | under |
| SL | $\{P\}\,c\,\{Q\}$ | $\llbracket c\rrbracket P \subseteq Q$ (heap) | $+\ \ast$, frame | fwd | over |
| ISL | $[P]\,c\,[\varepsilon{:}Q]$ | $\llbracket c\rrbracket_\varepsilon P \supseteq Q$ (heap) | $+\ \ast$, frame | fwd | under |
| SepSIL | $\langle P\rangle\,c\,\langle Q\rangle$ | $P \subseteq \llbracket c\rrbracket^{op}Q$ (heap) | $+\ \ast$, frame | bwd | under |

**Consequence-rule directions:** $\{$HL, SIL$\}$ strengthen-pre / weaken-post; $\{$IL, NC$\}$
weaken-pre / strengthen-post (governed by which side carries the $\forall$-over-a-set).

> Notation renders with a KaTeX markdown extension (Markdown Preview Enhanced / Markdown+Math).
