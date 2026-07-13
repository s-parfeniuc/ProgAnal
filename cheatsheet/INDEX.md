# Cheat sheet — page index

`ProgramAnalysis-cheatsheet.pdf` — **372 slides**, extracted page-for-page from the
original lecture PDFs (no cropping, no editing, no re-rendering) and merged in course order.

Slides marked **★** are the ones I'd protect if you need to cut the print down:
complete rule systems, core definitions, and the taxonomy tables.

| PDF page | Source deck | Slide | Content |
|---|---|---|---|
| | | | **— 1. Semantics: regular commands, collecting/relational/backward, wlp & wpp —** |
| 1 | 02-Denotational-v2 | 33 | Concrete domain (states) |
| 2 | 02-Denotational-v2 | 34 | Notation |
| 3 | 02-Denotational-v2 | 35 | Regular commands: syntax |
| 4 | 02-Denotational-v2 | 42 | Assertions / predicates vs sets |
| 5 | 02-Denotational-v2 | 45 | Collecting semantics |
| 6 | 02-Denotational-v2 | 46 | Atomic commands |
| 7 | 02-Denotational-v2 | 47 | Regular commands: collecting semantics |
| 8 | 02-Denotational-v2 | 49 | Encoding conditionals |
| 9 | 02-Denotational-v2 | 50 | Encoding while commands |
| 10 | 02-Denotational-v2 | 52 | Relational semantics |
| 11 | 02-Denotational-v2 | 54 | Regular commands (relational) |
| 12 | 02-Denotational-v2 | 55 | Backward semantics |
| 13 | 02-Denotational-v2 | 58 | Regular commands, backward |
| 14 | 02-Denotational-v2 | 59 | Hoare's wpp |
| 15 | 02-Denotational-v2 | 60 | wpp vs wlp |
| | | | **— 2. Hoare Logic —** |
| 16 | 03-HL | 24 | Floyd's axiom for assignment |
| 17 | 03-HL | 26 | Hoare's axiom for assignment |
| 18 | 03-HL | 27 | Forward vs backward assignment axioms |
| 19 | 03-HL | 43 | ★ The HL rules |
| 20 | 03-HL | 44 | HL validity |
| | | | **— 3. HL: total correctness, (in)completeness, minimal rules —** |
| 21 | 04-TotalCorrectness | 2 | The HL rules (recap) |
| 22 | 04-TotalCorrectness | 15 | Partial vs total correctness |
| 23 | 04-TotalCorrectness | 16 | Total correctness while rule |
| 24 | 04-TotalCorrectness | 17 | The two proof obligations |
| 25 | 04-TotalCorrectness | 27 | Which variant? |
| 26 | 04-TotalCorrectness | 28 | Lexicographic variants |
| 27 | 04-TotalCorrectness | 30 | Floyd's axiom: soundness proof |
| 28 | 04-TotalCorrectness | 32 | While rule: correctness proof |
| 29 | 04-TotalCorrectness | 33 | Incompleteness I (halting) |
| 30 | 04-TotalCorrectness | 34 | Incompleteness II (Godel) |
| 31 | 04-TotalCorrectness | 35 | Relative completeness |
| 32 | 04-TotalCorrectness | 37 | Adjoints: wlp |
| 33 | 04-TotalCorrectness | 38 | (Relative) completeness theorem |
| 34 | 04-TotalCorrectness | 42 | ★ HL: minimal set of rules |
| 35 | 04-TotalCorrectness | 43 | ★ HL: auxiliary rules |
| | | | **— 4. IL: consequence, dualities, agreement & denial —** |
| 36 | 05-IL-draft | 20 | Consequence rules explained (HL vs IL) |
| 37 | 05-IL-draft | 22 | Further dualities (drop conjuncts/disjuncts) |
| 38 | 05-IL-draft | 23 | Hoare's axiom is UNSOUND for IL |
| 39 | 05-IL-draft | 33 | HL vs IL: the duality slogan |
| 40 | 05-IL-draft | 41 | Principle of agreement |
| 41 | 05-IL-draft | 43 | Principle of denial |
| | | | **— 5. Real IL (ok/er) —** |
| 42 | 06-RealIL | 5 | The real IL (ok/er) |
| 43 | 06-RealIL | 6 | Exit conditions |
| 44 | 06-RealIL | 7 | Relational semantics with ok/er |
| 45 | 06-RealIL | 8 | Semantics: compositions (error short-circuit) |
| 46 | 06-RealIL | 9 | Shorthand notation |
| 47 | 06-RealIL | 10 | ★ Real IL rules |
| 48 | 06-RealIL | 11 | Atomic commands |
| 49 | 06-RealIL | 12 | Real atomic commands |
| 50 | 06-RealIL | 13 | Sequence |
| 51 | 06-RealIL | 14 | Choice: dropping disjuncts |
| 52 | 06-RealIL | 19 | Dealing with division (def) |
| 53 | 06-RealIL | 20 | Atomic commands (er) |
| 54 | 06-RealIL | 32 | Frame rule |
| 55 | 06-RealIL | 34 | Ghost variables + frame |
| | | | **— 6. IL metatheory + Necessary Conditions —** |
| 56 | 07-MoreIL-NC | 4 | ★ IL: minimal set of rules |
| 57 | 07-MoreIL-NC | 5 | ★ IL: auxiliary rules |
| 58 | 07-MoreIL-NC | 10 | IL (relative) completeness |
| 59 | 07-MoreIL-NC | 23 | Backward semantics |
| 60 | 07-MoreIL-NC | 31 | Which preconditions? |
| 61 | 07-MoreIL-NC | 32 | Sufficient preconditions |
| 62 | 07-MoreIL-NC | 33 | Necessary preconditions |
| 63 | 07-MoreIL-NC | 34 | Necessary conditions (NC) |
| 64 | 07-MoreIL-NC | 38 | Necessary conditions: definition |
| 65 | 07-MoreIL-NC | 41 | Comparison ignoring termination |
| 66 | 07-MoreIL-NC | 45 | ★ Compare the four logics |
| 67 | 07-MoreIL-NC | 46 | Which consequence rule? |
| 68 | 07-MoreIL-NC | 47 | HL vs NC: weakest/strongest |
| 69 | 07-MoreIL-NC | 48 | HL vs NC: the duality |
| 70 | 07-MoreIL-NC | 50 | HL vs NC (picture) |
| | | | **— 7. Sufficient Incorrectness Logic + the taxonomy —** |
| 71 | 08-SIL | 3 | The taxonomy |
| 72 | 08-SIL | 19 | Sufficient Incorrectness Logic (SIL) |
| 73 | 08-SIL | 25 | Manifest errors |
| 74 | 08-SIL | 26 | SIL rule: Hoare assignment |
| 75 | 08-SIL | 27 | SIL rule: assume |
| 76 | 08-SIL | 28 | SIL rule: choice |
| 77 | 08-SIL | 29 | SIL rule: iter |
| 78 | 08-SIL | 30 | SIL: dropping disjuncts in the pre |
| 79 | 08-SIL | 32 | ★ A proof system for SIL |
| 80 | 08-SIL | 33 | SIL soundness and completeness |
| 81 | 08-SIL | 35 | ★ The taxonomy (four quadrants) |
| 82 | 08-SIL | 36 | ★ Consequence rules (all four) |
| 83 | 08-SIL | 37 | SIL vs IL |
| 84 | 08-SIL | 38 | SIL vs HL |
| 85 | 08-SIL | 39 | SIL = HL if deterministic+terminating |
| | | | **— 8. Separation Logic —** |
| 86 | 09-SL | 12 | The 'points to' predicate |
| 87 | 09-SL | 21 | Ownership of a heap cell |
| 88 | 09-SL | 44 | Heap-manipulating atomic commands |
| 89 | 09-SL | 47 | Heaps: dom(h) |
| 90 | 09-SL | 48 | ★ Assertion language |
| 91 | 09-SL | 50 | Satisfaction: classical |
| 92 | 09-SL | 51 | ★ Satisfaction: structural (emp, |->, *) |
| 93 | 09-SL | 57 | Example: list segments |
| 94 | 09-SL | 58 | Inductive predicate ls |
| 95 | 09-SL | 59 | Separation Logic (SL) |
| 96 | 09-SL | 61 | SL principles |
| 97 | 09-SL | 62 | ★ Local axioms |
| 98 | 09-SL | 63 | In-place reasoning |
| 99 | 09-SL | 64 | Modified variables |
| 100 | 09-SL | 65 | Free variables |
| 101 | 09-SL | 66 | Some abbreviations |
| 102 | 09-SL | 70 | Local axiom: write |
| 103 | 09-SL | 71 | Local axiom: read |
| 104 | 09-SL | 74 | Local axiom: allocation |
| 105 | 09-SL | 90 | Example: list concatenation (setup) |
| 106 | 09-SL | 91 | Example: list concatenation |
| | | | **— 9. ISL + SepSIL —** |
| 107 | 10-ISL-SepSIL | 26 | SL relational semantics |
| 108 | 10-ISL-SepSIL | 27 | SL correctness + incompleteness |
| 109 | 10-ISL-SepSIL | 36 | Footprint property |
| 110 | 10-ISL-SepSIL | 38 | Footprint recipe |
| 111 | 10-ISL-SepSIL | 40 | Footprint FAILS in SL |
| 112 | 10-ISL-SepSIL | 41 | Information loss (resources must not shrink) |
| 113 | 10-ISL-SepSIL | 44 | ISL = IL + SL |
| 114 | 10-ISL-SepSIL | 45 | ISL regular commands |
| 115 | 10-ISL-SepSIL | 47 | ISL local axiom: write |
| 116 | 10-ISL-SepSIL | 48 | Reminder: reversed consequence |
| 117 | 10-ISL-SepSIL | 49 | ISL local axiom: read |
| 118 | 10-ISL-SepSIL | 50 | ISL local axiom: allocation |
| 119 | 10-ISL-SepSIL | 51 | ISL dispose (1st try) |
| 120 | 10-ISL-SepSIL | 52 | UNSOUND frame rule! |
| 121 | 10-ISL-SepSIL | 53 | Solution: track deallocated cells |
| 122 | 10-ISL-SepSIL | 54 | Satisfaction: structural (with x -/->) |
| 123 | 10-ISL-SepSIL | 55 | ISL local axiom: dispose |
| 124 | 10-ISL-SepSIL | 56 | Example: frame is now sound |
| 125 | 10-ISL-SepSIL | 57 | Footprint HOLDS in ISL |
| 126 | 10-ISL-SepSIL | 58 | ★ ISL additional local axioms (UAF, double free) |
| 127 | 10-ISL-SepSIL | 60 | ISL relational semantics (ok/er) |
| 128 | 10-ISL-SepSIL | 61 | ★ The ISL proof rules (CAV figure) |
| 129 | 10-ISL-SepSIL | 62 | ISL correctness + footprint |
| 130 | 10-ISL-SepSIL | 71 | SepSIL = SIL + SL |
| 131 | 10-ISL-SepSIL | 72 | SepSIL regular commands |
| 132 | 10-ISL-SepSIL | 73 | SepSIL assertions |
| 133 | 10-ISL-SepSIL | 74 | SepSIL local axiom: write |
| 134 | 10-ISL-SepSIL | 75 | SepSIL local axiom: read |
| 135 | 10-ISL-SepSIL | 76 | SepSIL local axiom: allocation |
| 136 | 10-ISL-SepSIL | 77 | SepSIL local axiom: dispose |
| 137 | 10-ISL-SepSIL | 84 | SepSIL relational semantics |
| 138 | 10-ISL-SepSIL | 85 | ★ Actual rules of SepSIL |
| 139 | 10-ISL-SepSIL | 86 | SepSIL correctness + completeness |
| | | | **— 10. Abstract Interpretation: the idea —** |
| 140 | 11-IntroAI-basic | 60 | Abstraction |
| 141 | 11-IntroAI-basic | 61 | Concretization |
| 142 | 11-IntroAI-basic | 62 | Signs abstraction (gamma) |
| 143 | 11-IntroAI-basic | 64 | Signs abstraction |
| 144 | 11-IntroAI-basic | 69 | Intervals abstraction |
| 145 | 11-IntroAI-basic | 70 | Best abstraction |
| 146 | 11-IntroAI-basic | 73 | Best abstraction (summary) |
| 147 | 11-IntroAI-basic | 74 | Relational abstractions |
| 148 | 11-IntroAI-basic | 78 | Best: not always possible |
| 149 | 11-IntroAI-basic | 86 | Analysis function |
| 150 | 11-IntroAI-basic | 89 | Sound analysis |
| 151 | 11-IntroAI-basic | 102 | Widening |
| 152 | 11-IntroAI-basic | 103 | Widening on convex polyhedra |
| 153 | 11-IntroAI-basic | 114 | Loop unrolling for precision |
| 154 | 11-IntroAI-basic | 115 | Abstract semantics at a glance |
| | | | **— 11. AI: formal setting, abstract operations —** |
| 155 | 12-IntroAI-formal | 5 | Yes / No / Don't know |
| 156 | 12-IntroAI-formal | 10 | Unsound analyses |
| 157 | 12-IntroAI-formal | 15 | Static analysis design |
| 158 | 12-IntroAI-formal | 16 | Sound abstractions |
| 159 | 12-IntroAI-formal | 18 | Abstract values |
| 160 | 12-IntroAI-formal | 24 | Domain refinement |
| 161 | 12-IntroAI-formal | 40 | Abstract operations |
| 162 | 12-IntroAI-formal | 41 | Transfer functions |
| 163 | 12-IntroAI-formal | 44 | The rule of signs |
| 164 | 12-IntroAI-formal | 48 | Correctness of abstract ops |
| 165 | 12-IntroAI-formal | 49 | Completeness of abstract ops |
| 166 | 12-IntroAI-formal | 55 | The abstract domain |
| 167 | 12-IntroAI-formal | 56 | The abstraction map |
| 168 | 12-IntroAI-formal | 57 | lub and glb |
| 169 | 12-IntroAI-formal | 58 | General definition |
| 170 | 12-IntroAI-formal | 59 | Analysis as fixpoint (equations) |
| 171 | 12-IntroAI-formal | 73 | Analysis as fixpoint |
| 172 | 12-IntroAI-formal | 82 | Abstract interpretation |
| | | | **— 12. Order theory + Galois connections (Ex.1-12) —** |
| 173 | 13-Galois-v2 | 22 | lub and glb |
| 174 | 13-Galois-v2 | 29 | Convergence and ACC |
| 175 | 13-Galois-v2 | 31 | CPOs |
| 176 | 13-Galois-v2 | 33 | Complete lattices |
| 177 | 13-Galois-v2 | 39 | Order theory: summary |
| 178 | 13-Galois-v2 | 50 | Abstraction and concretization |
| 179 | 13-Galois-v2 | 55 | Concrete domain |
| 180 | 13-Galois-v2 | 56 | Abstract domain |
| 181 | 13-Galois-v2 | 57 | Ingredients of AI |
| 182 | 13-Galois-v2 | 61 | Sound approximation |
| 183 | 13-Galois-v2 | 63 | Concretization function |
| 184 | 13-Galois-v2 | 74 | Sound abstraction |
| 185 | 13-Galois-v2 | 77 | Abstraction function (needs meet) |
| 186 | 13-Galois-v2 | 79 | ★ Galois connection |
| 187 | 13-Galois-v2 | 82 | GC but not GI |
| 188 | 13-Galois-v2 | 83 | GIs from GCs |
| 189 | 13-Galois-v2 | 84 | Galois connection (formal) |
| 190 | 13-Galois-v2 | 87 | Absence of best abstraction |
| 191 | 13-Galois-v2 | 91 | Ex.1 Extensivity |
| 192 | 13-Galois-v2 | 94 | Ex.2 Reductivity |
| 193 | 13-Galois-v2 | 97 | Ex.3 Monotonicity |
| 194 | 13-Galois-v2 | 99 | Ex.4 Equivalent definition |
| 195 | 13-Galois-v2 | 103 | Ex.5 Round-trips |
| 196 | 13-Galois-v2 | 105 | Ex.6 Idempotency |
| 197 | 13-Galois-v2 | 107 | Ex.7 gamma induces alpha |
| 198 | 13-Galois-v2 | 109 | Ex.8 alpha induces gamma |
| 199 | 13-Galois-v2 | 113 | Ex.9 alpha preserves lubs |
| 200 | 13-Galois-v2 | 115 | Ex.10 gamma preserves glbs |
| 201 | 13-Galois-v2 | 119 | Ex.11 surjectivity <=> GI |
| 202 | 13-Galois-v2 | 121 | Ex.12 injectivity <=> GI |
| | | | **— 13. Abstract domains + BCA —** |
| 203 | 14-AbstractDomains | 6 | Galois insertion as closures |
| 204 | 14-AbstractDomains | 12 | ★ Operator approximation (3 equivalent forms) |
| 205 | 14-AbstractDomains | 13 | Operator approximation (equivalences) |
| 206 | 14-AbstractDomains | 16 | Sound approximations |
| 207 | 14-AbstractDomains | 17 | ★ Best correct approximation (bca) |
| 208 | 14-AbstractDomains | 19 | Sound operator composition (theorem) |
| 209 | 14-AbstractDomains | 20 | BCA composition? (remark) |
| 210 | 14-AbstractDomains | 22 | Abstract domains |
| 211 | 14-AbstractDomains | 23 | General considerations |
| 212 | 14-AbstractDomains | 35 | Constant domain (gamma/alpha) |
| 213 | 14-AbstractDomains | 36 | Constant domain |
| 214 | 14-AbstractDomains | 47 | Constant set domain |
| 215 | 14-AbstractDomains | 57 | Intervals structure |
| 216 | 14-AbstractDomains | 58 | BCAs for sum |
| 217 | 14-AbstractDomains | 61 | Convergence of the analysis (ACC) |
| 218 | 14-AbstractDomains | 66 | Take home message |
| | | | **— 14. Domains, products, fixpoint approximation —** |
| 219 | 15-AbstractAnalysis | 6 | Congruence domain |
| 220 | 15-AbstractAnalysis | 9 | Congruence domain structure |
| 221 | 15-AbstractAnalysis | 10 | Congruence BCAs |
| 222 | 15-AbstractAnalysis | 14 | Convex polyhedra domain |
| 223 | 15-AbstractAnalysis | 17 | No best approximation |
| 224 | 15-AbstractAnalysis | 19 | Octagons domain |
| 225 | 15-AbstractAnalysis | 23 | Classification of domains |
| 226 | 15-AbstractAnalysis | 30 | Cartesian product domain |
| 227 | 15-AbstractAnalysis | 33 | Reduced product domain |
| 228 | 15-AbstractAnalysis | 37 | Smashed point-wise lifting |
| 229 | 15-AbstractAnalysis | 41 | Abstract stores |
| 230 | 15-AbstractAnalysis | 44 | Abstract denotational semantics |
| 231 | 15-AbstractAnalysis | 46 | Accelerated abstract interpreter |
| 232 | 15-AbstractAnalysis | 49 | Correctness of abstract operations |
| 233 | 15-AbstractAnalysis | 50 | Completeness |
| 234 | 15-AbstractAnalysis | 51 | Completeness and bcas |
| 235 | 15-AbstractAnalysis | 53 | |.| is not complete on Int |
| 236 | 15-AbstractAnalysis | 54 | Fixpoint approximation (sound) |
| 237 | 15-AbstractAnalysis | 55 | Fixpoint approximation (complete) |
| 238 | 15-AbstractAnalysis | 73 | Accelerated abstract analysis |
| | | | **— 15. Local Completeness Logic —** |
| 239 | 16-LCL | 4 | Completeness, revisited |
| 240 | 16-LCL | 12 | Local completeness |
| 241 | 16-LCL | 17 | Sources of incompleteness |
| 242 | 16-LCL | 18 | Completeness for guards (necessary cond.) |
| 243 | 16-LCL | 20 | Completeness for guards (nec. + suff.) |
| 244 | 16-LCL | 26 | Local completeness equation |
| 245 | 16-LCL | 27 | Local completeness (why local) |
| 246 | 16-LCL | 29 | ★ LCL triples (vs O'Hearn's) |
| 247 | 16-LCL | 31 | LCL: atomic commands |
| 248 | 16-LCL | 33 | LCL: locally incomplete guard (Int) |
| 249 | 16-LCL | 35 | Convexity lemma |
| 250 | 16-LCL | 37 | Consequence rule [relax] |
| 251 | 16-LCL | 40 | ★ The proof system LCL_A (Fig. 3) |
| 252 | 16-LCL | 41 | LCL: sequential composition |
| 253 | 16-LCL | 42 | LCL: choice |
| 254 | 16-LCL | 45 | LCL validity |
| 255 | 16-LCL | 46 | Logical correctness |
| 256 | 16-LCL | 47 | ★ Verification theorem (correctness or true bug) |
| 257 | 16-LCL | 48 | Logical completeness |
| 258 | 16-LCL | 49 | Intrinsic logical incompleteness |
| 259 | 16-LCL | 50 | Over vs under |
| | | | **— 16. Control Flow Analysis for FUN (0-CFA, constraints, k-CFA) —** |
| 260 | CFA-for-FUN | 18 | CFA of FUN: syntax |
| 261 | CFA-for-FUN | 19 | Example 1: labelling |
| 262 | CFA-for-FUN | 22 | The Control Flow Analysis |
| 263 | CFA-for-FUN | 23 | CFA as a constraint-based analysis |
| 264 | CFA-for-FUN | 25 | CFA: overview |
| 265 | CFA-for-FUN | 26 | Abstract domains: informally |
| 266 | CFA-for-FUN | 28 | Abstract domains: formally |
| 267 | CFA-for-FUN | 31 | The specification of a solution |
| 268 | CFA-for-FUN | 32 | ★ Acceptability relation |
| 269 | CFA-for-FUN | 33 | Clause: constants |
| 270 | CFA-for-FUN | 34 | Clause: variables |
| 271 | CFA-for-FUN | 35 | Clause: fn |
| 272 | CFA-for-FUN | 36 | Clause: fun |
| 273 | CFA-for-FUN | 38 | Clause: conditional |
| 274 | CFA-for-FUN | 39 | Clause: binary operation |
| 275 | CFA-for-FUN | 41 | Clause: let |
| 276 | CFA-for-FUN | 47 | ★ Clause: application (recap) |
| 277 | CFA-for-FUN | 56 | Inclusions |
| 278 | CFA-for-FUN | 61 | Coinductive nature of the CFA |
| 279 | CFA-for-FUN | 62 | This is a 0-CFA |
| 280 | CFA-for-FUN | 78 | Semantic correctness |
| 281 | CFA-for-FUN | 81 | Terms and expressions |
| 282 | CFA-for-FUN | 87 | ★ SOS I |
| 283 | CFA-for-FUN | 88 | ★ SOS II |
| 284 | CFA-for-FUN | 90 | New CFA clauses (close/bind) |
| 285 | CFA-for-FUN | 91 | Relation between environments (R) |
| 286 | CFA-for-FUN | 92 | Relation between values (V) |
| 287 | CFA-for-FUN | 93 | Subject reduction (theorem) |
| 288 | CFA-for-FUN | 104 | Comparing analyses (the order) |
| 289 | CFA-for-FUN | 106 | Moore family |
| 290 | CFA-for-FUN | 107 | Existence of a least CFA |
| 291 | CFA-for-FUN | 108 | Existence: corollaries |
| 292 | CFA-for-FUN | 110 | Coinduction vs induction (idea) |
| 293 | CFA-for-FUN | 111 | Coinduction vs induction |
| 294 | CFA-for-FUN | 115 | ★ Syntax-directed specification |
| 295 | CFA-for-FUN | 116 | Syntax-directed spec (why) |
| 296 | CFA-for-FUN | 118 | SD clause: fn |
| 297 | CFA-for-FUN | 119 | SD clause: recursive functions |
| 298 | CFA-for-FUN | 120 | SD clause: application |
| 299 | CFA-for-FUN | 121 | Syntax-directed CFA (summary) |
| 300 | CFA-for-FUN | 128 | Preservation: finite universe Lab*/Var*/Term* |
| 301 | CFA-for-FUN | 129 | Preservation: the bounded universe |
| 302 | CFA-for-FUN | 131 | Preservation of solutions (prop.) |
| 303 | CFA-for-FUN | 134 | Existence (Moore family for |=s) |
| 304 | CFA-for-FUN | 152 | Constraint-based 0-CFA |
| 305 | CFA-for-FUN | 154 | Constraints: constants |
| 306 | CFA-for-FUN | 155 | Constraints: variables |
| 307 | CFA-for-FUN | 156 | Constraints: functions |
| 308 | CFA-for-FUN | 158 | Constraints: application (explained) |
| 309 | CFA-for-FUN | 159 | Constraints: application |
| 310 | CFA-for-FUN | 160 | ★ Constraint-based CFA (summary) |
| 311 | CFA-for-FUN | 163 | Complexity of the constraints |
| 312 | CFA-for-FUN | 166 | Preservation of solutions (constraints) |
| 313 | CFA-for-FUN | 174 | The constraint solver |
| 314 | CFA-for-FUN | 175 | The algorithm |
| 315 | CFA-for-FUN | 180 | Algorithm pseudocode (1) |
| 316 | CFA-for-FUN | 181 | Algorithm pseudocode (2) |
| 317 | CFA-for-FUN | 186 | Algorithm pseudocode (3,4) |
| 318 | CFA-for-FUN | 199 | Back to ex.1: the solution |
| 319 | CFA-for-FUN | 201 | Correctness of the algorithm |
| 320 | CFA-for-FUN | 206 | CFA + DFA |
| 321 | CFA-for-FUN | 207 | CFA+DFA abstract domains |
| 322 | CFA-for-FUN | 208 | CFA+DFA abstract operators |
| 323 | CFA-for-FUN | 210 | CFA+DFA acceptability |
| 324 | CFA-for-FUN | 214 | To recap |
| 325 | CFA-for-FUN | 220 | Abstract values as complete lattices |
| 326 | CFA-for-FUN | 221 | Monotone structure (definition) |
| 327 | CFA-for-FUN | 228 | CFA with abstract values as lattices |
| 328 | CFA-for-FUN | 230 | Correctness of the analysis |
| 329 | CFA-for-FUN | 237 | Uniform k-CFA |
| 330 | CFA-for-FUN | 239 | Abstract domains: contexts |
| 331 | CFA-for-FUN | 241 | Context-sensitive abstract values |
| 332 | CFA-for-FUN | 243 | k-CFAs |
| 333 | CFA-for-FUN | 245 | k-CFA acceptability relation |
| 334 | CFA-for-FUN | 249 | k-CFA clause: application (explained) |
| 335 | CFA-for-FUN | 250 | k-CFA clause: application |
| 336 | CFA-for-FUN | 251 | Uniform k-CFA (summary) |
| 337 | CFA-for-FUN | 259 | Correctness and implementation of k-CFA |
| 338 | CFA-for-FUN | 260 | Complexity of uniform k-CFA |
| 339 | CFA-for-FUN | 262 | Complexity of 0-CFA |
| 340 | CFA-for-FUN | 268 | Cartesian Product Algorithm |
| 341 | CFA-for-FUN | 279 | The evolution of CFA for FUN |
| | | | **— 17. Control Flow Analysis for the pi-calculus —** |
| 342 | CFA-for-Pi | 6 | pi-calculus: prefixes |
| 343 | CFA-for-Pi | 9 | pi-calculus: syntax |
| 344 | CFA-for-Pi | 13 | Structural congruence |
| 345 | CFA-for-Pi | 14 | Reduction semantics |
| 346 | CFA-for-Pi | 19 | Abstract domains |
| 347 | CFA-for-Pi | 20 | Abstract domains (cont.) |
| 348 | CFA-for-Pi | 22 | The specification of a solution |
| 349 | CFA-for-Pi | 27 | Clause: out |
| 350 | CFA-for-Pi | 30 | Clause: in |
| 351 | CFA-for-Pi | 31 | Clause: tau |
| 352 | CFA-for-Pi | 33 | Clause: par |
| 353 | CFA-for-Pi | 34 | Clause: sum |
| 354 | CFA-for-Pi | 35 | Clause: match |
| 355 | CFA-for-Pi | 36 | Clause: res |
| 356 | CFA-for-Pi | 37 | Clause: rep |
| 357 | CFA-for-Pi | 38 | ★ CFA clauses for pi-calculus |
| 358 | CFA-for-Pi | 43 | Semantic correctness |
| 359 | CFA-for-Pi | 46 | Congruence + substitution + subject reduction |
| 360 | CFA-for-Pi | 47 | Existence (Moore family) |
| 361 | CFA-for-Pi | 53 | Polyadic: specification |
| 362 | CFA-for-Pi | 63 | Well-behavedness |
| 363 | CFA-for-Pi | 64 | Adequacy: well-behaved |
| 364 | CFA-for-Pi | 68 | Well-sortedness |
| 365 | CFA-for-Pi | 69 | Adequacy: well-sorted |
| 366 | CFA-for-Pi | 72 | Secrecy: dynamic property |
| 367 | CFA-for-Pi | 73 | Secrecy-preserving processes |
| 368 | CFA-for-Pi | 75 | Non-leaking: dynamic property |
| 369 | CFA-for-Pi | 76 | Non-leaking processes |
| 370 | CFA-for-Pi | 79 | Taint safety: definition |
| 371 | CFA-for-Pi | 80 | Taint-safe processes |
| 372 | CFA-for-Pi | 85 | The CFA pattern |
