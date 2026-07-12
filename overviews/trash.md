Two separate things there. Let me take them in turn.

1. What object satisfies ACC
The lattice from §2 — the "complete lattice of proposed solutions" — comes in two versions, and only the restricted one is finite.

Unrestricted (what $\models$ lives on):
$$L ;=; \widehat{\mathit{Cache}}\times\widehat{\mathit{Env}} ;=; \big(\mathbf{Lab}\to\wp(\mathbf{Term})\big)\times\big(\mathbf{Var}\to\wp(\mathbf{Term})\big)$$
where $\mathbf{Lab},\mathbf{Var},\mathbf{Term}$ are the full sets of all labels, all variables, all closures. This is a complete lattice (pointwise products of powersets always are) — so the least solution exists — but it is infinite and does not satisfy ACC: e.g. ${t_1}\subsetneq{t_1,t_2}\subsetneq{t_1,t_2,t_3}\subsetneq\cdots$ is an infinite strictly-ascending chain.

Restricted to fragments (what $\models_s$ effectively lives on):
$$L_\ast ;=; \big(\mathbf{Lab}\ast\to\wp(\mathbf{Term}\ast)\big)\times\big(\mathbf{Var}\ast\to\wp(\mathbf{Term}\ast)\big)$$
with $\mathbf{Lab}\ast,\mathbf{Var}\ast,\mathbf{Term}_\ast$ all read off the finite syntax tree. Now:

$\mathbf{Term}\ast$ finite $\Rightarrow$ $\wp(\mathbf{Term}\ast)$ is a finite lattice;
a finite-indexed product ($\mathbf{Lab}\ast, \mathbf{Var}\ast$ finite) of finite lattices is finite;
a finite lattice trivially satisfies ACC — there are only finitely many elements, so any ascending chain must stop climbing.
So the answer to your question: it is $L_\ast$, the complete lattice of guesses restricted to the fragments of $e^\ast$, that becomes ACC. In the example that's $\big({1,\dots,5}\to\wp{C_x,C_y}\big)\times\big({x,y}\to\wp{C_x,C_y}\big)$ — a finite lattice of size $4^5\cdot 4^2$.

Why ACC is the thing you need (vs. completeness). These are two different guarantees, don't conflate them:

property	comes from	buys you
complete lattice	pointwise powerset structure (§3, Moore family)	the least solution exists
ACC (finiteness)	restricting to fragments of $e^\ast$	the least solution is computable
Fixpoint iteration starts at $\bot=(\lambda l.\varnothing,\lambda x.\varnothing)$ and repeatedly applies the monotone constraint functional $F$: $\bot\sqsubseteq F(\bot)\sqsubseteq F^2(\bot)\sqsubseteq\cdots$. This is an ascending chain, so ACC forces it to stabilize after finitely many steps, and the stable point is the least solution. On the infinite $L$ the same chain need not stabilize — the lfp is still there (completeness), you just can't reach it by finite iteration. Restricting to fragments is exactly what turns "exists" into "computable."

2. "Stated over all intermediate expressions"
This is about the third argument of the judgement. The relation has the shape
$$(\hat C,\hat\rho);\models; ie,$$
and the question is what $ie$ is allowed to be.

The program $e^\ast$ runs by substitution. When $(\mathsf{fn},x\Rightarrow e_0)$ is applied to a value $v$, the semantics reduces to $e_0[v/x]$ — a new expression that is not literally a subterm of $e^\ast$. These reducts (and their reducts, …) are the intermediate expressions $\mathbf{IExp}$: everything reachable from $e^\ast$ by evaluation, an in-general infinite set.

Why $\models$ must be defined on all of them: the whole content of semantic correctness (14) is a subject-reduction statement,
$$(\hat C,\hat\rho)\models e \ \text{ and }\ e\to e' \quad\Longrightarrow\quad (\hat C,\hat\rho)\models e',$$
"acceptability is preserved as the program runs." To even write $\models e'$ you need $\models$ to accept the reduct $e'$ as its argument — i.e. $\models$ is a relation on $(\widehat{\mathit{Cache}}\times\widehat{\mathit{Env}})\times\mathbf{IExp}$, not on $(\ldots)\times{\text{subterms of }e^\ast}$. That generality is what "stated over all intermediate expressions" means: the judgement form ranges $ie$ over $\mathbf{IExp}$, so its $\hat C,\hat\rho$ have to be prepared to index any label/variable that could appear in some reduct — the full $\mathbf{Lab},\mathbf{Var}$, hence the infinite $L$.

Why the extra range is harmless on a program term. The saving grace of this labelling discipline: β-reduction only copies existing subterms, it never invents new labels or new closures. So every label appearing in any reduct of $e^\ast$ is already in $\mathbf{Lab}\ast$, every closure already in $\mathbf{Term}\ast$. Consequently, when you apply $\models$ (or $\models_s$) to the actual program $e^\ast$, no constraint ever mentions a label/variable outside $\mathbf{Lab}\ast,\mathbf{Var}\ast$. At every index outside those finite sets there is simply no constraint, so the least solution — being the smallest — assigns $\varnothing$ there. Deleting those permanently-$\varnothing$ coordinates changes nothing: the least solution of the wide $\models$ and the least solution of the restricted $\models_s$ agree on $\mathbf{Lab}\ast,\mathbf{Var}\ast$ and are $\varnothing$ elsewhere. That is the sense in which "the extra range is sent to $\varnothing$ and the two least solutions coincide."

So: $\models$ is stated widely because the correctness proof has to talk about the program mid-evaluation (through its reducts); $\models_s$ is stated narrowly because it is only ever run on the fixed finite tree of $e^\ast$ — and preservation is the theorem that says running it narrowly loses nothing.

