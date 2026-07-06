---
title: Denotational Semantics
type: note
status: full
source: "lectures/ProgramAnalysis-02-Denotational-v2.pdf"
tags: [semantics, collecting-semantics, foundations]
---

# Denotational Semantics

> **One line.** Give each piece of syntax a mathematical **meaning** `⟦·⟧` (a value
> or a function on states), so we can reason about programs rigorously instead of
> guessing intent — semantics = *assigning meaning to syntax*.

Syntax is *how a program is written* (`IV`, `four`, `quattro`); semantics is *the
computed object* (`⟦IV⟧ = ⟦four⟧ = ⟦quattro⟧ = 4`). Natural language is ambiguous
("I won't take long" = *respect your time* **or** *I have lots to say*); we want the
rigorous side, hence the double brackets `⟦·⟧`.

---

## 0. States and the concrete domain

- A **variable set** `X`; values are integers `ℤ`. See [[glossary]].
- A **state** (store) is a total function `σ : X → ℤ` giving every variable a value.
  Notation `σ = [x ↦ 2, y ↦ 3]` means `x` is `2`, `y` is `3`, **all others `0`**.
  Order doesn't matter; `[x ↦ 2, x ↦ 3]` is *not* a valid state (a function is single-valued).
- **All states:** `Σ ≜ { σ : X → ℤ }`.
- **State update** `σ[n/x]` (also written `σ[x ↦ n]`): like `σ` but `x` now holds `n`.
$$\sigma[n/x](y) \;\triangleq\; \begin{cases} n & \text{if } x = y \\ \sigma(y) & \text{otherwise}\end{cases}$$

### Concrete domain
> **Intuition.** The universe of *exact* information we could ever want about a program:
> every possible **set of states**. A single `P ⊆ Σ` is a **state property** (the states where it holds).

**Formal.** The concrete domain is the powerset of all states, ordered by `⊆`:
$$\wp(\Sigma) \;\triangleq\; \{\, P \mid P \subseteq \Sigma \,\}$$
This is the "ground truth" domain that [[intro-abstract-interpretation|abstract interpretation]] will later approximate — hence *concrete*.

---

## 1. The assertion language (meaning of expressions & predicates)

Three syntactic categories (see [[glossary]] for the grammar symbols):
```
a ::= n | x | a1 + a2 | ...            (arithmetic, Aexp)
b ::= a1 ≤ a2 | b1 ∧ b2 | ¬b | ...     (boolean,    Bexp)
```

### Arithmetic expressions — meaning is a *number* (a function of the state)
$$\llbracket \cdot \rrbracket : \mathsf{Aexp} \to \Sigma \to \mathbb{Z}$$
`⟦a⟧σ` evaluates `a` in state `σ`. Defined by structural recursion:
$$\llbracket n\rrbracket\sigma \triangleq n \qquad \llbracket x\rrbracket\sigma \triangleq \sigma(x) \qquad \llbracket a_0\ \texttt{op}\ a_1\rrbracket\sigma \triangleq \llbracket a_0\rrbracket\sigma \;\mathit{op}\; \llbracket a_1\rrbracket\sigma$$
> [!note] Syntax vs meaning of operators
> Left `op` is a **syntactic** symbol; right `op` (italic) is the **mathematical** operation. The brackets `⟦·⟧` translate one into the other.

*Example:* `⟦2x²+3y+5xz⟧[x↦1,y↦2,z↦1] = 13`; the same expr on `[x↦1]` (others `0`) `= 2`.

### Boolean expressions — meaning is a *set of states* (collecting version)
$$\llbracket \cdot \rrbracket : \mathsf{Bexp} \to \wp(\Sigma) \to \wp(\Sigma)$$
`⟦b⟧P` = "**intuitively `b ∧ P`**": the states of `P` that also satisfy `b`. It *filters* `P`.
$$\llbracket\texttt{true}\rrbracket P \triangleq P \qquad \llbracket\texttt{false}\rrbracket P \triangleq \varnothing \qquad \llbracket\texttt{not } b\rrbracket P \triangleq P \setminus (\llbracket b\rrbracket P)$$
$$\llbracket a_0\ \texttt{cmp}\ a_1\rrbracket P \triangleq \{\, \sigma \in P \mid \llbracket a_0\rrbracket\sigma\ \mathit{cmp}\ \llbracket a_1\rrbracket\sigma \,\} \qquad \llbracket b_0\ \texttt{bop}\ b_1\rrbracket P \triangleq \llbracket b_0\rrbracket P\ \mathit{bop}\ \llbracket b_1\rrbracket P$$
> [!important] Lemma
> `⟦b⟧P ⊆ P` — filtering never adds states. (Splits `P` into the `b` part and the `¬b` part.)

### Predicates vs sets
> **Intuition.** A logical predicate and "the set of states making it true" are **two views of the same thing**. We freely switch between them.

**Formal.** A predicate `P` denotes the set of states satisfying it:
$$\{\sigma \vDash P\} \;=\; \{\, \sigma \mid \llbracket P\rrbracket\sigma = \texttt{true} \,\}$$
Examples: `(x = 1) ↔ {σ | σ(x)=1}`, `(x ≤ y) ↔ {σ | σ(x) ≤ σ(y)}`. This is why in
[[hoare-logic]] we can write `⟦c⟧P ⊆ Q` — pre/postconditions *are* sets of states.

---

## 2. Meaning of a command

A command's meaning is a **state transformer**. Three progressively richer views:

| View | Type | Non-termination |
|---|---|---|
| Deterministic | `⟦c⟧ : Σ → Σ_⊥` | `⟦c⟧σ = ⊥` |
| Nondeterministic | `⟦c⟧ : Σ → ℘(Σ)` | `⟦c⟧σ = ∅` |
| **Collecting** | `⟦c⟧ : ℘(Σ) → ℘(Σ)` | contributes `∅` |

- **Deterministic:** one input state → one output state, or `⊥` if it loops forever.
  `Σ_⊥ ≜ Σ ⊎ {⊥}` (lift: all states **plus** a bottom element `⊥` for divergence). See [[glossary]].
- **Nondeterministic:** a program may branch (lack of info, approximation, or the
  choice construct `c₁ + c₂`), so one input → a **set** of possible outputs; `∅` = never terminates.
- **Collecting semantics:** run *all* input states of `P` at once —
$$\llbracket c\rrbracket P \;=\; \bigcup_{\sigma \in P} \llbracket c\rrbracket \sigma$$
  We write `⟦c⟧σ` as shorthand for `⟦c⟧{σ}`. This is the workhorse for [[hoare-logic]] and [[intro-abstract-interpretation]].

> [!note] Regular commands (this course's syntax)
> `c ::= e | c₁ ; c₂ | c₁ + c₂ | c⋆`  with atomic `e ::= skip | x := a | b?`
> — sequencing `;`, **choice** `+`, **Kleene star** `⋆`, and the **guard/assume** `b?`. This is a
> regular-expression–style presentation of control flow.

---

## 3. Partial correctness
> **Intuition.** "The program never produces a **wrong** answer — but it's allowed to
> run forever." Nothing is promised about termination; only that *if* it stops, it stops in a good state.

**Formal.** Given precondition `P` and postcondition `Q` (a *correctness specification*):
$$\{P\}\, c\, \{Q\} \quad\text{iff}\quad \llbracket c\rrbracket P \subseteq Q \quad\text{iff}\quad \forall \sigma \in P.\ \llbracket c\rrbracket\sigma \text{ either diverges or lands in } Q$$
"No undesirable state is reached." This is exactly the [[hoare-logic]] triple. It is
an **over-approximation** stance: `Q` is a superset of the reachable outputs.

---

## 4. Weakest liberal precondition (Dijkstra)
> **Intuition.** Turn the question around: given program `c` and spec `Q`, what is the
> **largest** set of "safe" input states I can start from and still be partially correct?
> "Liberal" = divergence is tolerated (matches partial correctness).

**Formal.**
$$wlp(c, Q) \;\triangleq\; \{\, \sigma \mid \llbracket c\rrbracket\{\sigma\} \subseteq Q \,\}$$
It is the set of **all and only** partially-correct input states. Key characterization:
$$P \subseteq wlp(c, Q) \quad\Longleftrightarrow\quad \llbracket c\rrbracket P \subseteq Q$$
This is a **Galois-connection**-shaped adjunction between `⟦c⟧` and `wlp(c,·)` (foreshadows [[galois-connections]]):
$$\llbracket c\rrbracket(wlp(c,Q)) \subseteq Q \qquad\qquad wlp(c, \llbracket c\rrbracket P) \supseteq P$$
`wlp` is **backward** (from `Q` to inputs); `⟦c⟧` is **forward** — cf. Floyd vs Hoare assignment in [[hoare-logic]].

*Example (slide):* `⟦x := x+1⟧(x+1 > 30) ⊆ (x > 0)` because `{x | x+1 > 30} ⊆ {x | x+1 > 0}`.
*Divisors example:* `wlp(c, s ∈ {2,3}) = (x ∈ {1,4,6,9}) ∪ (x prime)`.

### 4b. `wpp` vs `wlp` — "possible" vs "liberal" (∃ vs ∀)
Lecture 2 introduces a **second** precondition alongside `wlp`, through the
backward/relational view of `⟦c⟧` (slides 53–64).

**Backward semantics (slides 53–55).** View the command as a relation
`⟦c⟧ ⊆ Σ × Σ`, `⟦c⟧ = {(σ,δ) | δ ∈ ⟦c⟧σ}`. Its **converse** is the *backward
semantics* `⟦c⟧ᵒᵖ = {(δ,σ) | (σ,δ) ∈ ⟦c⟧}`, so `δ ∈ ⟦c⟧σ ⟺ σ ∈ ⟦c⟧ᵒᵖ δ`.
Applied to a set, `⟦c⟧ᵒᵖ Q` is the **pre-image**: the inputs that *can* reach `Q`.

> **Intuition.** Same question — "which inputs are safe for `Q`?" — under two quantifiers:
> - `wlp` (Dijkstra, *liberal*): inputs whose computations are **all** successful (∀).
> - `wpp` (Hoare, *possible*): inputs that have **a** successful computation (∃).

$$wlp(c,Q) = \{\, \sigma \mid \llbracket c\rrbracket\{\sigma\} \subseteq Q \,\} \qquad\qquad wpp(c,Q) = \{\, \sigma \mid \llbracket c\rrbracket\sigma \cap Q \neq \varnothing \,\}$$

- `wlp` = "largest set of inputs whose computations are **all** successful."
- `wpp` = "largest set of inputs that have **a** successful computation reaching `Q`",
  equivalently the pre-image `wpp(c,Q) = ⟦c⟧ᵒᵖ Q` (slide 59).

**Duality (De Morgan).** They are complementary (`‾·` = complement in `Σ`):
$$wpp(c,Q) = \overline{wlp(c,\overline{Q})}$$
because "some output in `Q`" = "not (all outputs in `¬Q`)".

> [!example] Worked example (slides 62–63)
> `c ≜ (z := x) + (z := y)` (nondeterministic choice), so `z` becomes `x` **or** `y`.
> Then `z = 0` is guaranteed by **all** runs iff both are `0`, but **possible** iff either is:
> - `wlp(c, z=0) = (x=0 ∧ y=0)` — the ∀/`∧` case
> - `wpp(c, z=0) = (x=0 ∨ y=0)` — the ∃/`∨` case

**No adjunction (slide 64, "Question 3").** Unlike `wlp` (§4), composing `wpp` with
`⟦c⟧` gives **neither** inclusion in general:
- `⟦c⟧(wpp(c,Q)) ?? Q` → **none**: *some states in `Q` can be unreachable*.
- `wpp(c, ⟦c⟧P) ?? P` → **none**: *some states in `P` can non-terminate*.

**Where each is used.** `wlp` (∀, over-approximation) → partial correctness, [[hoare-logic]].
`wpp` (∃, reachability / under-approximation) → proving a behaviour is *possible* — the seed of [[incorrectness-logic]].

> [!note] Don't confuse `wpp` with the total-correctness `wp`
> The classical **Dijkstra weakest precondition** `wp` (demonic **+** guaranteed
> termination) is a *third*, different notion that pairs with [[total-correctness]]
> (*lect. 04*). This course's `wpp` is **existential / possible**, not the terminating one.

---

## 5. Exactness vs approximation
> **Intuition.** The exact reachable set `⟦c⟧P` is usually uncomputable, so we settle
> for a set that is either **too big** (safe for proving *absence* of behaviour) or
> **too small** (safe for proving *presence* of behaviour).

**Formal.** For a computed/claimed `Q` vs the true `⟦c⟧P`:
- **Exact:** `⟦c⟧P = Q`.
- **Over-approximation:** `⟦c⟧P ⊆ Q` — `Q` may include unreachable states; **can't miss** a real behaviour → proves *no bad state is reachable* (used by [[hoare-logic]], [[intro-abstract-interpretation]]).
- **Under-approximation:** `⟦c⟧P ⊇ Q` — every state of `Q` is genuinely reachable; **no false positives** → proves *a behaviour really happens* (used by [[incorrectness-logic]]).

> [!example] Non-termination analysis (why the direction matters)
> Does `⟦c⟧σ = ∅` (loops forever)?
> - **Over-approx** `Q ⊇ ⟦c⟧σ` with `Q ⊆ ∅` ⟹ `⟦c⟧σ = ∅` → **proves non-termination**.
> - **Under-approx** `Q ⊆ ⟦c⟧σ` with `Q ⊋ ∅` ⟹ some state reachable → **proves termination**.

---

## 6. Symbol dictionary (exhaustive for this lecture)

| Symbol | Reading / meaning |
|---|---|
| `⟦·⟧` | **semantic brackets**: map syntax → its mathematical meaning |
| `⟦a⟧σ` | value of arithmetic expr `a` in state `σ` (a number in `ℤ`) |
| `⟦b⟧P` | states of `P` satisfying boolean `b` (a subset of `P`) |
| `⟦c⟧` | meaning of command `c` (a state transformer) |
| `⟦c⟧σ`, `⟦c⟧P` | output state(s) from input `σ` / input set `P` |
| `σ` | a **state** / store, `σ : X → ℤ` |
| `σ(x)` | value of variable `x` in state `σ` |
| `[x ↦ 2, y ↦ 3]` | state literal (listed vars; all others `0`) |
| `σ[n/x]`, `σ[x ↦ n]` | **state update** (`x` becomes `n`, rest unchanged) |
| `X` | set of program variables |
| `ℤ`, `ℕ`, `𝔹` | integers, naturals, booleans |
| `Σ` | set of **all** states, `{σ : X → ℤ}` |
| `Σ_⊥` | `Σ ⊎ {⊥}` — states plus divergence |
| `⊥` | **bottom**: non-terminating execution |
| `℘(Σ)` | powerset of states = **concrete domain** |
| `P`, `Q` | a set of states = a **property** = a predicate |
| `σ ⊨ P` | state `σ` **satisfies** predicate `P` (`⟦P⟧σ = true`) |
| `⊆`, `⊇`, `=` | set inclusion / equality (approximation ordering) |
| `∪`, `⋃_{σ∈P}` | union / indexed big union |
| `\` | set difference (used for `¬b`) |
| `∅` | empty set (no reachable state / divergence in collecting view) |
| `≜` | "is defined as" |
| `⊎` | disjoint union |
| `wlp(c, Q)` | weakest **liberal** precondition: **all** computations reach `Q` (∀) |
| `wpp(c, Q)` | weakest **possible** precondition: **a** computation reaches `Q` (∃); `= ⟦c⟧ᵒᵖ Q` |
| `⟦c⟧ᵒᵖ` | backward semantics: converse relation of `⟦c⟧`; `⟦c⟧ᵒᵖ Q` = pre-image of `Q` |
| `∩`, `≠ ∅` | intersection; "is inhabited" (used in `wpp`) |
| `‾·` | complement in `Σ` (De Morgan duality of `wlp`/`wpp`) |
| `::=`, `\|` | grammar production / alternative |
| `;` | sequential composition of commands |
| `+` | nondeterministic **choice** `c₁ + c₂` |
| `⋆` | **Kleene star** `c⋆` (iterate zero+ times) |
| `b?` | **guard / assume**: proceed only if `b` holds |
| `op` / *op* | syntactic operator / its mathematical meaning |
| `cmp`, `bop` | generic comparison / boolean operator |
| `∧`, `¬`, `≤` | logical and, not, comparison |
| `∃`, `∀` | exists, for all |
| `→` | function-type arrow |
| `Aexp`, `Bexp` | syntactic categories of arithmetic / boolean expressions |

---

## Links
Feeds [[hoare-logic]] (`⟦c⟧P ⊆ Q`), [[total-correctness]] (adds termination),
[[incorrectness-logic]] (under-approximation), and [[intro-abstract-interpretation]] /
[[galois-connections]] (the concrete domain `℘(Σ)` and the `⟦c⟧`/`wlp` adjunction). See [[glossary]].
