---
title: CFA for the π-calculus — the Calculus & 0-CFA
abbrev: CFA (π)
lectures: "22 Part 2, 23 (CFA for π); master deck: CFA-for-Pi"
paper: "Bodei, Degano, Nielson & Nielson — CFA for the π-calculus; Milner, The Polyadic π-calculus"
theme: "extending CFA from higher-order functions to concurrency: predicting communications"
oneliner: "0-CFA for the π-calculus computes (ρ̂,κ̂): which names each variable may hold and which names may travel on each channel — a sound over-approximation of all communications."
render: "Notation is LaTeX math ($…$ / $$…$$). Preview with a KaTeX markdown extension."
---

# CFA for the π-calculus — the Calculus & 0-CFA

**Theme:** the second CFA strand. The same "specify an acceptable over-approximation" pattern from
[13](13-cfa-motivation-0cfa-specification.md) is applied to **concurrency**: instead of "which
functions reach which call sites," we compute **"which names travel on which channels"** — the
communication structure of a mobile concurrent system. Applications (security, taint) are
[19](19-cfa-pi-applications.md).

## 1. Purpose & core idea
The **π-calculus** models concurrent processes that communicate by passing **names** (channels)
over channels — **name mobility**, so the communication topology *changes at runtime*. As with
higher-order dispatch, you cannot read it off the syntax. CFA computes a **sound
over-approximation of all possible communications**: for every channel, which names may be sent
on it, and for every input variable, which names it may become bound to.

## 2. The π-calculus (syntax & semantics)
$$\pi ::= \bar u\langle v\rangle\ (\text{send }v\text{ on }u)\ \mid\ u(x)\ (\text{receive on }u,\text{ bind }x)\ \mid\ \tau\ (\text{internal})$$
$$P ::= \mathbf 0 \mid \pi.P \mid [x{=}y]P\ (\text{match}) \mid (\nu n)P\ (\text{restriction}) \mid \textstyle\sum_{i\in I}\pi_i.P_i\ (\text{guarded choice}) \mid P_1\mid P_2 \mid\ !P\ (\text{replication}).$$
The only **binders** are input $u(x)$ and restriction $(\nu n)$; processes are taken up to
$\alpha$-renaming; we analyse **closed** processes. Semantics = **structural congruence** $\equiv$
(parallel is an Abelian monoid; scope-extrusion laws; $!P\equiv P\mid !P$; $[x{=}x]P\equiv P$) plus
a **reduction** relation:
$$[\textsf{Com}]\ (\bar n\langle m\rangle.P + P')\mid(n(x).Q + Q')\to P\mid Q[m/x]\qquad [\textsf{Tau}]\ (\tau.P+Q)\to P$$
$$[\textsf{Res}]\ \dfrac{P\to P'}{(\nu n)P\to(\nu n)P'}\quad [\textsf{Par}]\ \dfrac{P\to P'}{P\mid Q\to P'\mid Q}\quad [\textsf{Eq}]\ \dfrac{P\equiv Q\ \ Q\to Q'\ \ Q'\equiv P'}{P\to P'}$$
**Scope extrusion** ($(\nu z)(\bar x\langle z\rangle.P)\mid x(y).Q\to(\nu z)(P\mid Q[z/y])$) is what
makes names *mobile* — a private channel's scope widens as it is communicated.

## 3. 0-CFA for the π-calculus
**Abstract domains** — a pair $(\hat\rho,\hat\kappa)$ of *global* maps ($\widehat{\mathit{Val}}=\wp(\mathit{Const})$):
$$\hat\rho:\mathit{Var}\to\wp(\mathit{Const})\ (\text{names a variable may be bound to},\ \hat\rho(n)=\{n\}),\qquad \hat\kappa:\mathit{Const}\to\wp(\mathit{Const})\ (\text{names that may travel on each channel}).$$
Acceptability has one clause per **action** ($\models_A$) and per **process** ($\models_P$); it is
acceptable if it **safely over-approximates every communication**.

> [!important] The communication clauses
> **Output** — record what may be sent on every channel the subject may denote:
> $$[\textsf{out}]\ (\hat\rho,\hat\kappa)\models_A\bar u\langle v\rangle \iff \forall n\in\hat\rho(u):\ \hat\rho(v)\subseteq\hat\kappa(n).$$
> **Input** — bind $x$ to everything that may arrive on every channel $u$ may denote:
> $$[\textsf{in}]\ (\hat\rho,\hat\kappa)\models_A u(x) \iff \forall n\in\hat\rho(u):\ \hat\kappa(n)\subseteq\hat\rho(x).$$
> **Processes:** $\models_P\mathbf 0$ always; $\models_P P_1\mid P_2\iff\models_P P_1\wedge\models_P P_2$;
> $\models_P\sum_i\pi_i.P_i\iff\bigwedge_i(\models_A\pi_i\wedge\models_P P_i)$; $\models_P(\nu n)P\iff\models_P P$;
> $\models_P\,!P\iff\models_P P$; match $[x{=}y]P$ requires $\models_P P$ (guarded by possible equality of $\hat\rho(x),\hat\rho(y)$).
> Together, $[\textsf{out}]$/$[\textsf{in}]$ over a shared channel $n$ give $\hat\kappa(n)\subseteq\hat\rho(x)$ — **the analysis threads a sent name to the receiver's variable**, predicting the communication.

*Example:* for $(\bar a\langle b\rangle.P'+\bar a\langle d\rangle.P')\mid a(w).\bar c\langle w\rangle.Q'$,
the least solution has $\hat\kappa(a)\supseteq\{b,d\}$ and $\hat\rho(w)\supseteq\{b,d\}$ — both
possible communications are captured.

## 4. Properties — correctness & existence
- **Semantic correctness (subject reduction).** If $(\hat\rho,\hat\kappa)\models_P P$ and $P\to P'$
  (up to $\equiv$), then $(\hat\rho,\hat\kappa)\models_P P'$: acceptability is **preserved by
  reduction**, so the global $(\hat\rho,\hat\kappa)$ soundly describes *all* reachable communications
  (same pattern as [14](14-0cfa-semantic-correctness.md)). Because $\hat\rho,\hat\kappa$ are global,
  no configuration bookkeeping is needed.
- **Existence & least solution.** Acceptable solutions form a **Moore family** (complete lattice,
  pointwise $\subseteq$), so a **least, most precise** analysis exists — as for FUN
  ([15](15-0cfa-existence-least-solutions.md)); it is computed by the analogous constraint solving.
- **Imprecision** is inherent (0-CFA merges by name, not by context); it can be sharpened with
  contexts/polyadic extensions.

## 5. Peculiarities & connections
- **CFA predicts communications** — the key deliverable; $\hat\kappa$ is essentially an
  over-approximate "who-talks-to-whom on what."
- **Global domains** ($\hat\rho,\hat\kappa$ not per-point) fit the flat, name-based nature of the
  calculus; identity of names is preserved (as function identity was in FUN).
- Same **Flow Logic** recipe as [13](13-cfa-motivation-0cfa-specification.md) (specify + validate +
  least solution) — CFA is a *pattern*, instantiated here for concurrency.
- **Polyadic π-calculus** (sending tuples of names) is a routine extension; it underlies the
  applications ([19](19-cfa-pi-applications.md)).

## 6. Pros / cons / use cases
- **Pros:** sound, static prediction of communication topology for mobile concurrent systems;
  reuses the whole CFA framework; global domains keep it simple.
- **Cons:** 0-CFA imprecision (name-merging); models are idealised (π-calculus).
- **Use cases:** analysing concurrent/distributed and cryptographic protocols; the basis for the
  **security** analyses of [19](19-cfa-pi-applications.md).

---

## 📋 Cheatsheet (complete)

### π-calculus syntax
$$\pi ::= \bar u\langle v\rangle\mid u(x)\mid\tau,\qquad P ::= \mathbf 0\mid\pi.P\mid[x{=}y]P\mid(\nu n)P\mid\textstyle\sum_{i}\pi_i.P_i\mid P_1\mid P_2\mid\ !P.$$
Binders: $u(x)$, $(\nu n)$; closed processes; up to $\alpha$-renaming.

### Semantics
$\equiv$: $\mid$ Abelian monoid, scope laws, $!P\equiv P\mid !P$, $[x{=}x]P\equiv P$.
$$[\textsf{Com}]\ (\bar n\langle m\rangle.P{+}P')\mid(n(x).Q{+}Q')\to P\mid Q[m/x];\quad [\textsf{Tau}],[\textsf{Res}],[\textsf{Par}],[\textsf{Eq}];\quad \text{scope extrusion} = \text{mobility}.$$

### 0-CFA domains
$$\hat\rho:\mathit{Var}\to\wp(\mathit{Const})\ (\hat\rho(n)=\{n\}),\qquad \hat\kappa:\mathit{Const}\to\wp(\mathit{Const})\ (\text{channel}\to\text{names sent}).$$

### Clauses (predict communications)
$$[\textsf{out}]\ \forall n\in\hat\rho(u):\hat\rho(v)\subseteq\hat\kappa(n)\qquad [\textsf{in}]\ \forall n\in\hat\rho(u):\hat\kappa(n)\subseteq\hat\rho(x)$$
$$\models_P\mathbf 0\ \text{(true)};\ \models_P P_1\mid P_2=\models_P P_1\wedge\models_P P_2;\ \models_P\textstyle\sum_i\pi_i.P_i=\bigwedge_i(\models_A\pi_i\wedge\models_P P_i);\ \models_P(\nu n)P=\models_P\,!P=\models_P P.$$

### Theorems
- **[Correctness]** $(\hat\rho,\hat\kappa)\models_P P\wedge P\to P'\Rightarrow(\hat\rho,\hat\kappa)\models_P P'$ (subject reduction).
- **[Existence]** acceptable solutions are a Moore family ⟹ least (best) CFA exists.
