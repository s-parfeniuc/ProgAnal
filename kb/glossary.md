---
title: Glossary
type: reference
---

# Glossary — symbols & terms

Short definitions with a link to where the concept is developed. Grows as the course does.

## Notation
| Symbol | Reading | Where |
|---|---|---|
| `⟦·⟧` | **semantic brackets**: map syntax to its mathematical meaning | [[denotational-semantics]] |
| `⟦c⟧` | denotational / collecting semantics of command `c`; here a **map on sets of states** `℘(Σ) → ℘(Σ)` | [[denotational-semantics]] |
| `⟦c⟧P` | the set of states reachable by running `c` from some state in `P` | [[hoare-logic]] |
| `⟦a⟧σ`, `⟦b⟧P` | value of arith. expr `a` in `σ`; states of `P` satisfying `b` | [[denotational-semantics]] |
| `σ` | a **state** / store, `σ : X → ℤ`; `σ(x)` = value of `x` | [[denotational-semantics]] |
| `Σ`, `Σ_⊥` | all states; all states plus `⊥` (divergence) | [[denotational-semantics]] |
| `⊥` | **bottom**: non-terminating execution | [[denotational-semantics]] |
| `σ[n/x]`, `σ[x↦n]` | **state update** (`x` becomes `n`, rest unchanged) | [[denotational-semantics]] |
| `℘(Σ)` | powerset of states = **concrete domain** | [[denotational-semantics]] |
| `σ ⊨ P` | state `σ` **satisfies** predicate `P` (`⟦P⟧σ = true`) | [[denotational-semantics]] |
| `wlp(c,Q)` | weakest **liberal** precondition: **all** computations reach `Q` (∀); `{σ \| ⟦c⟧σ ⊆ Q}` | [[denotational-semantics]] |
| `wpp(c,Q)` | weakest **possible** precondition: **a** computation reaches `Q` (∃); `{σ \| ⟦c⟧σ ∩ Q ≠ ∅}` | [[denotational-semantics]] |
| `⟦c⟧ᵒᵖ` | backward semantics (converse relation); `⟦c⟧ᵒᵖ Q` = pre-image, `= wpp(c,Q)` | [[denotational-semantics]] |
| `wp(c,Q)` | *classical* weakest precondition (total correctness: demonic + terminating) — distinct from `wpp` | [[total-correctness]] |
| `≜` | "is defined as"; `⊎` disjoint union; `\` set difference | [[denotational-semantics]] |
| `;` `+` `⋆` `b?` | seq. composition, choice, Kleene star, guard/assume | [[denotational-semantics]] |
| `{P} c {Q}` | **Hoare triple** (partial correctness): from `P`, if `c` halts, `Q` holds | [[hoare-logic]] |
| `[P] c [Q]` | **incorrectness triple** (O'Hearn): `⟦c⟧P ⊇ Q`, under-approximation | [[incorrectness-logic]] |
| `[P] c [ε: Q]` | IL triple with **exit condition** `ε ∈ {ok, er}` (normal / erroneous) | [[real-incorrectness-logic]] |
| `(P) c (Q)` | **necessary-condition triple**: `⟦c⟧ᵒᵖ Q ⊆ P` (backward, over-approx) | [[il-nc]] |
| `def(a)` | **definedness** of expression `a` (e.g. `def(a₁/a₂) = … ∧ a₂≠0`) | [[real-incorrectness-logic]] |
| `error()`, `x:=nondet()` | bug / nondeterminism primitives added for IL | [[incorrectness-logic]] |
| `t`, `z` | loop **variant** (ranking function) and its fresh ghost snapshot | [[total-correctness]] |
| `G/B/I` | good / bad / infinite program traces from a state | [[il-nc]] |
| `P[a/x]` | syntactic substitution of `a` for `x` in `P` | [[hoare-logic]] |
| `⊑`, `⊔`, `⊓` | partial order, join (lub), meet (glb) in a lattice | [[galois-connections]] |
| `⊤`, `⊥` | top, bottom of a lattice | [[galois-connections]] |
| `α`, `γ` | abstraction and concretization maps of a Galois connection | [[galois-connections]] |
| `α ⊣ γ` | `α` is the lower adjoint of `γ` (Galois connection) | [[galois-connections]] |
| `∗` | separating conjunction | [[separation-logic]] |
| `Σ` | set of program states (stores / memories) | [[denotational-semantics]] |
| `⊆` (on `℘(Σ)`) | set inclusion = **over-approximation** ordering | [[hoare-logic]] |

## Terms
- **Concrete domain** — `℘(Σ)`, every possible set of states; the exact universe AI approximates. See [[denotational-semantics]].
- **Assertion language** — syntax of expressions/predicates with `⟦·⟧` semantics; a predicate = a set of states. See [[denotational-semantics]].
- **Predicates vs sets** — `P` and `{σ | ⟦P⟧σ = true}` are two views of one thing. See [[denotational-semantics]].
- **Partial correctness** — postcondition holds *if* the program terminates: `⟦c⟧P ⊆ Q`. See [[denotational-semantics]], [[hoare-logic]].
- **Weakest liberal precondition** — `wlp(c,Q)`: inputs whose computations **all** reach `Q` (∀). See [[denotational-semantics]].
- **Weakest possible precondition** — `wpp(c,Q)`: inputs with **a** computation reaching `Q` (∃); the pre-image `⟦c⟧ᵒᵖ Q`; De Morgan dual of `wlp`. See [[denotational-semantics]].
- **Backward semantics** — converse relation `⟦c⟧ᵒᵖ`; `δ ∈ ⟦c⟧σ ⟺ σ ∈ ⟦c⟧ᵒᵖ δ`. See [[denotational-semantics]].
- **Weakest precondition (classical `wp`)** — total-correctness notion (demonic + terminating); **distinct** from the course's `wpp`. See [[total-correctness]].
- **Total correctness** — partial correctness **+** termination. See [[total-correctness]].
- **Exactness vs approximation** — exact `=`, over-approx `⊆` (no missed behaviour), under-approx `⊇` (no false positives). See [[denotational-semantics]].
- **Over-approximation** — a superset of the reachable states; the basis of soundness in HL / AI. `⟦c⟧P ⊆ Q`.
- **Under-approximation** — a subset of the reachable states; the basis of [[incorrectness-logic]] (true bugs, no false positives).
- **Variant (ranking function)** — a below-bounded, strictly decreasing measure proving loop termination. See [[total-correctness]].
- **Necessary vs sufficient precondition** — sufficient (`wlp`): if it holds, correct; necessary (NC): if violated, inevitably incorrect. See [[il-nc]].
- **Approximation square** — Forward/Backward × Over/Under: HL, IL, NC (+ 1 open quadrant). See [[il-nc]].
- **Agreement / denial** — bridges letting an [[incorrectness-logic|IL]] derivation refute an [[hoare-logic|HL]] spec (a real bug). See [[incorrectness-logic]].
- **Collecting semantics** — run all input states at once: `⟦c⟧P = ⋃_{σ∈P} ⟦c⟧σ`. See [[denotational-semantics]].
- **Loop invariant** — assertion preserved by the loop body: `{P ∧ b} c {P}`. See [[hoare-logic]].
- **Inference rule** — `premises / conclusion`; a rule with no premises is an **axiom**. See [[hoare-logic]].
- **Derivation tree** — proof built by composing inference rules. See [[hoare-logic]].
- **Soundness** — every derivable judgement is valid (semantically true).
- **Completeness** — every valid judgement is derivable.
