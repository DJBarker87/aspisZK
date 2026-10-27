# Rc11 mechanical recount

Candidate `AspisR1.ARX_Root.deployed` is proved and remains unadopted. Actual adopted root: `AspisR1.Rc10_Top.deployed`. No proof was added. **The deployed 100-bit target is not yet established.**

The complete fresh kernel types are [before](Rc11_BEFORE.lean.txt) and [after](Rc11_AFTER.lean.txt); the named ARX declaration and full axioms lines are in Rc11_001/stdout.log. Rc11_002/stdout.log reprints all 44 Rc10 inventories and expands the changed account/runtime definitions. Every retained printed block matches modulo whitespace (Rc11_inventory-check.json).

## Counting method

One row is one quantified atomic law family. Split conjunction leaves; preserve shared existentials, SAME returned execution witnesses, implication guards and installation slots. Do not multiply a Fin22 law into 22 rows. Count conditional finish laws even when hidden in returned continuations. Native-local L142–L146 and source-global F3Y_G_L142–L146 are ten independent families. Returned facts are not assumed premises. Data-only fields are inventoried below and add no atomic law. T=adopted external trust; P=proof/budget condition; G=approved game/accepted-event clause; C=vacuity-suspect. Owner means accountable cone, not completed work.

## Fresh side-by-side totals

| Basis | Rc10 T/P/G/C | ARX candidate T/P/G/C | Delta |
|---|---|---|---|
| actual antecedent | 83/12/13/0 | 83/11/13/0 | 0/-1/0/0 |
| deployment only | 6/4/0/0 | 6/3/0/0 | 0/-1/0/0 |
| deployment alias | 0/1/0/0 | 0/0/0/0 | 0/-1/0/0 |
| deployment-inclusive non-alias | 89/16/13/0 | 89/14/13/0 | 0/-2/0/0 |

Raw and distinct counts coincide within each root after excluding deployment alias L185=L159. Raw totals including that alias are 89T/17P/13G/0C before and 89T/14P/13G/0C after: −3 raw P rows but **−2 distinct P families**. Independent runtime/P data binders earn no P deletion credit. Actual adopted delta is **zero**.

| Owner (deployment-inclusive, non-alias) | Rc10 T/P/G/C | ARX T/P/G/C |
|---|---|---|
| external | 89/1/0/0 | 89/1/0/0 |
| session A | 0/10/0/0 | 0/10/0/0 |
| lead | 0/5/13/0 | 0/3/13/0 |

## Every row absent from the candidate

| Row or binder | Before | After | Class/owner/count |
|---|---|---|---|
| L159 `binding` | `F3T_Runtime.StoredCarrierBinding ... P runtime`: entire accepted runtime run equals canonical annotated installed-source experiment | No root hypothesis; admitted account observer and derived charge domination | P, lead, −1 actual |
| L185 | Deployment alias of L159 | Absent with L159 | P, lead, alias only |
| L181 | Residual experiment/native-prefix and ordered-query association | Account/admitted query and rejected-prefix transport composed | P, lead, −1 deployment |
| `runtime : F3T_Runtime.Runtime` | Independent data argument | Defined `ARX_AdmittedRuntime.runtime ... a` | Data-only experiment binder, lead; 0 atomic rows |
| `P : F3T_ByteCarrier.ByteProver` | Independent data argument | Defined `ARW_Induced.program ... a` | Data-only experiment binder, lead; 0 atomic rows |

L181 credit concerns the admitted experiment/native-prefix association only. It does not establish source-to-ELF correspondence or L166 complete native Result/effects fidelity. L166, L187 and L188 remain P. This is no global exact frozen2 log equality claim.

## Every candidate-only or specialized binder

| Exact binder | Definition/classification | Atomic addition |
|---|---|---|
| `a : SCE_Experiment.Adversary A` | Arbitrary data, game-role (lead), fixed before H. Fields: `first : Program Bytes State (FirstInputs A)` and `second : FirstInputs A → Vec U8 → Heap (Nat → Record) → A → Program Bytes State (SecondInputs A)`. No Prop law fields. | 0 T/P/G/C |
| `let P := ARW_Induced.program native1 copy allocator CPH_Program.verifier a` | Defined ByteProver; data-only game specialization (lead). Retains both reached adversary phases; returns original first submission. | 0 |
| `queries : ∀ H : Bytes → State, (ARW_Induced.issued native1 copy allocator CPH_Program.verifier a H).length ≤ Q0+Q1` | L154, P/external, unchanged budget family at induced P by `ARW_Induced.queries`; Q=Q0+Q1 is an upper bound, not exact per-path work. | 0 |
| `let runtime := ARX_AdmittedRuntime.runtime (Tx := Tx) L copy allocator c indexError reservation native1 native2 hashv a` | Defined admitted-image observer; data/game definition (lead), not a trusted universal support premise. | 0 |

There is no independent Q function binder in ARX. `Q0 Q1 : Nat` are retained verbatim. The induced-P/issued-Q relationship is the printed theorem `ARW_Induced.queries`. Labeling data as game-role does not invent extra class-G atomic assumptions; the existing thirteen G rows remain thirteen.

## Statement and semantic comparison

**No new propositional premise is added that is not an Rc10 specialization.** L154 is exactly the old query inequality at induced P. All other retained antecedents and all conditional continuation laws are unchanged. Rc11_statement-check.json checks the complete source declaration against an explicit replacement whitelist, and checks byte identity from `let select` through the final conclusion. Rc11_statement.diff records every edit.

No constant, carrier TYPE, collision-event constructor, extractor or conclusion SCHEMA differs. Literal closed propositions do differ: P and runtime are now defined terms; the failure functional is evaluated on the admitted observer rather than an independently supplied runtime, and the event is instantiated at induced P. Thus this is not a proof that ARX is a direct instantiation of Rc10 (its removed binding is not supplied), nor equality with arbitrary unfiltered runtimes. The draft amendment makes that definition choice explicit.

The observer returns the original RunView on exactly the cylinders with their OWN `ARU_Support.At` witnesses. Unfolded membership includes two runtime admissions, both native successes, their own bank/game/RuntimePersistence tuple and first/second query-restricted source agreement. They are body membership data, not new universal root antecedents. The unrelated fixed native tuple in the root is not asserted to be the outcome of every a. `ARX_Domain.range` proves the exact image; `ARX_AdmittedRuntime.on_admitted` and `ARX_LawEquivalence.observations/work/mean/failure_mean` establish equality on admitted executions and original-weight zero extension. Outside admission the returned option is None; all issued logs remain (`ARX_RejectedPrefixes.cost`) and source rejection has zero mass (`ARX_RejectedPrefixes.mass`). No conditioning/renormalization is performed. `ARX_OldClassPoison.differs` rules out equating the two observers even for the old pure-second-choice class. No unfiltered global mean equality is claimed.

## Every retained atomic row, side by side

Each row below is present in both roots. L154 is marked specialized; all other 115 retained row statements/families are unchanged. The JSON retains the original exact definition references, jobs, guards and blocker notes.

| ID | Class | Owner | Scope | Rc10 meaning | ARX disposition |
|---|---|---|---|---|---|
| L001 | T | external | actual antecedent | For related valid local states: data-cell identity | same family and guards |
| L002 | T | external | actual antecedent | For related valid local states: lamports-cell identity | same family and guards |
| L003 | T | external | actual antecedent | For related valid local states: shared data-cell alias agreement | same family and guards |
| L004 | T | external | actual antecedent | For related valid local states: live data/lamports separation | same family and guards |
| L005 | T | external | actual antecedent | For related valid local states: typed cell payload equality | same family and guards |
| L006 | T | external | actual antecedent | For related valid local states: counter equality | same family and guards |
| L007 | T | external | actual antecedent | For related valid local states: live-guard lookup equality | same family and guards |
| L008 | T | external | actual antecedent | For related valid local states: live guard identity | same family and guards |
| L009 | T | external | actual antecedent | For related valid local states: allocation liveness | same family and guards |
| L010 | T | external | actual antecedent | For related valid local states: descriptor identity | same family and guards |
| L011 | T | external | actual antecedent | Exact typed transition and reply; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | same family and guards |
| L012 | T | external | actual antecedent | Successor library state relates to specified heap; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | same family and guards |
| L013 | T | external | actual antecedent | Exact typed transition and reply; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | same family and guards |
| L014 | T | external | actual antecedent | Successor library state relates to specified heap; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | same family and guards |
| L015 | T | external | actual antecedent | Exact typed transition and reply; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | same family and guards |
| L016 | T | external | actual antecedent | Successor library state relates to specified heap; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | same family and guards |
| L017 | T | external | actual antecedent | Exact typed transition and reply; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | same family and guards |
| L018 | T | external | actual antecedent | Successor library state relates to specified heap; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | same family and guards |
| L019 | T | external | actual antecedent | Exact typed transition and reply; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | same family and guards |
| L020 | T | external | actual antecedent | Successor library state relates to specified heap; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | same family and guards |
| L021 | T | external | actual antecedent | Exact typed transition and reply; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | same family and guards |
| L022 | T | external | actual antecedent | Successor library state relates to specified heap; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | same family and guards |
| L023 | T | external | actual antecedent | Exact typed transition and reply; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | same family and guards |
| L024 | T | external | actual antecedent | Successor library state relates to specified heap; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | same family and guards |
| L025 | T | external | actual antecedent | Exact typed transition and reply; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | same family and guards |
| L026 | T | external | actual antecedent | Successor library state relates to specified heap; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | same family and guards |
| L027 | T | external | actual antecedent | Exact typed transition and reply; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | same family and guards |
| L028 | T | external | actual antecedent | Successor library state relates to specified heap; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | same family and guards |
| L029 | T | external | actual antecedent | Exact typed transition and reply; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | same family and guards |
| L030 | T | external | actual antecedent | Successor library state relates to specified heap; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | same family and guards |
| L031 | T | external | actual antecedent | Exact typed transition and reply; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | same family and guards |
| L032 | T | external | actual antecedent | Successor library state relates to specified heap; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | same family and guards |
| L033 | T | external | actual antecedent | Exact typed transition and reply; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | same family and guards |
| L034 | T | external | actual antecedent | Successor library state relates to specified heap; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | same family and guards |
| L035 | T | external | actual antecedent | Copy equals the full slice-copy specification, including panic and frame | same family and guards |
| L036 | T | external | actual antecedent | TX1 initial heap: pairwise distinct live tokens | same family and guards |
| L037 | T | external | actual antecedent | TX1 initial heap: pairwise distinct live owners | same family and guards |
| L038 | T | external | actual antecedent | TX1 initial heap: minCounter ≤ counter | same family and guards |
| L039 | T | external | actual antecedent | TX1 initial heap: counter ≤ maxCounter | same family and guards |
| L040 | T | external | actual antecedent | TX1 initial heap: counter = external + shared count − exclusive count | same family and guards |
| L041 | T | external | actual antecedent | TX1 initial heap: tracked exclusive implies external = 0 | same family and guards |
| L042 | T | external | actual antecedent | TX1 initial heap: tracked exclusive implies no tracked shared guard | same family and guards |
| L043 | T | external | actual antecedent | TX1 initial heap: tracked exclusive implies exclusive count = 1 | same family and guards |
| L044 | T | external | actual antecedent | TX1 initial heap: negative external implies shared count = 0 | same family and guards |
| L045 | T | external | actual antecedent | TX1 initial heap: negative external implies exclusive count = 0 | same family and guards |
| L046 | T | external | actual antecedent | TX1 initial heap: each live guard has an allocated cell | same family and guards |
| L047 | T | external | actual antecedent | TX1 initial heap: each live guard descriptor equals the payload descriptor | same family and guards |
| L048 | T | external | actual antecedent | TX1 initial heap: live account data and lamports cells differ | same family and guards |
| L049 | T | external | actual antecedent | TX1 initial heap: live account data cell is allocated | same family and guards |
| L050 | T | external | actual antecedent | TX1: no initial tracked guards | same family and guards |
| L051 | T | external | actual antecedent | TX1: external counter is zero | same family and guards |
| L052 | T | external | actual antecedent | TX1: all admitted account owners live | same family and guards |
| L053 | T | external | actual antecedent | TX1: all admitted account counters zero | same family and guards |
| L054 | T | external | actual antecedent | TX1: shared data cell implies equal keys | same family and guards |
| L055 | T | external | actual antecedent | TX1: equal keys imply shared data cell | same family and guards |
| L056 | T | external | actual antecedent | TX1 concrete library state relates to entry heap | same family and guards |
| L057 | T | external | actual antecedent | TX2 initial heap: pairwise distinct live tokens | same family and guards |
| L058 | T | external | actual antecedent | TX2 initial heap: pairwise distinct live owners | same family and guards |
| L059 | T | external | actual antecedent | TX2 initial heap: minCounter ≤ counter | same family and guards |
| L060 | T | external | actual antecedent | TX2 initial heap: counter ≤ maxCounter | same family and guards |
| L061 | T | external | actual antecedent | TX2 initial heap: counter = external + shared count − exclusive count | same family and guards |
| L062 | T | external | actual antecedent | TX2 initial heap: tracked exclusive implies external = 0 | same family and guards |
| L063 | T | external | actual antecedent | TX2 initial heap: tracked exclusive implies no tracked shared guard | same family and guards |
| L064 | T | external | actual antecedent | TX2 initial heap: tracked exclusive implies exclusive count = 1 | same family and guards |
| L065 | T | external | actual antecedent | TX2 initial heap: negative external implies shared count = 0 | same family and guards |
| L066 | T | external | actual antecedent | TX2 initial heap: negative external implies exclusive count = 0 | same family and guards |
| L067 | T | external | actual antecedent | TX2 initial heap: each live guard has an allocated cell | same family and guards |
| L068 | T | external | actual antecedent | TX2 initial heap: each live guard descriptor equals the payload descriptor | same family and guards |
| L069 | T | external | actual antecedent | TX2 initial heap: live account data and lamports cells differ | same family and guards |
| L070 | T | external | actual antecedent | TX2 initial heap: live account data cell is allocated | same family and guards |
| L071 | T | external | actual antecedent | TX2: no initial tracked guards | same family and guards |
| L072 | T | external | actual antecedent | TX2: external counter is zero | same family and guards |
| L073 | T | external | actual antecedent | TX2: all admitted account owners live | same family and guards |
| L074 | T | external | actual antecedent | TX2: all admitted account counters zero | same family and guards |
| L075 | T | external | actual antecedent | TX2: shared data cell implies equal keys | same family and guards |
| L076 | T | external | actual antecedent | TX2: equal keys imply shared data cell | same family and guards |
| L077 | T | external | actual antecedent | TX2 concrete library state relates to entry heap | same family and guards |
| L078 | T | external | actual antecedent | Native TX1 function equals owned extracted stage1 at the exact installed dictionary | same family and guards |
| L079 | T | external | actual antecedent | Native TX2 function equals owned extracted stage2 at the exact installed dictionary | same family and guards |
| L080 | T | external | actual antecedent | op43 equals the emitted digest wrapper around hashv | same family and guards |
| L081 | T | external | actual antecedent | ∀ bytes, sha256 bytes = H bytes, inside the ideal-oracle realization | same family and guards |
| L082 | T | external | actual antecedent | Every successful hashv decodes to sha256 of the exact flattened parts | same family and guards |
| L083 | G | lead | actual antecedent | TX1 wrapper returns the given inner Ok, post heap and allocator state; event restriction, not a universal-success obligation | same family and guards |
| L084 | G | lead | actual antecedent | TX2 wrapper returns the given inner Ok, post heap and allocator state; event restriction, not a universal-success obligation | same family and guards |
| L142 | P | session A | actual antecedent | For the SAME native view/prepared/data, every successful newWeights, alpha-slice and pair return decodes to the model dot of final values with both dual folds of FunctionalWeights. | same family and guards |
| L143 | P | session A | actual antecedent | ∀ j : Fin 22, foldWord alpha0 (batchedWord W gamma) (q j) = V(q j) | same family and guards |
| L144 | P | session A | actual antecedent | first semantic polynomial boundary equals claim; under SAME EquationEndpoint view/claim/polys parsing guards | same family and guards |
| L145 | P | session A | actual antecedent | ∀ j : Fin 9, next boundary equals previous evaluation at challenge; under SAME EquationEndpoint view/claim/polys parsing guards | same family and guards |
| L146 | P | session A | actual antecedent | last semantic evaluation equals exact masked spend terminal; under SAME EquationEndpoint view/claim/polys parsing guards | same family and guards |
| L154 | P | external | actual antecedent | ∀ H : Bytes → State, (eval H P).1.length ≤ Q0 + Q1. Bound on all issued ByteProver oracle queries including repeats, uniformly over ideal worlds; external adversary budget condition, not a cryptographic axiom or proved concrete deployment budget. | same L154 at induced P (issued equality) |
| L166 | P | lead | deployment only | Accepted-path source Result/effects association; both rejected prefixes reject and every earlier oracle read is counted, under the owner-approved success-conditioned ruling. | same family and guards |
| L187 | P | lead | deployment only | Only coherent cached focused composition audited; full frozen dependency release replay not run. | same family and guards |
| L188 | P | lead | deployment only | Current top standard-axiom audit passes; final release dependency/trust/adoption audit remains. | same family and guards |
| L189 | T | external | deployment only | Retained release/tool/runtime/cryptographic trust; not an additional explicit Lean binder. | same family and guards |
| L190 | T | external | deployment only | Retained release/tool/runtime/cryptographic trust; not an additional explicit Lean binder. | same family and guards |
| L191 | T | external | deployment only | Retained release/tool/runtime/cryptographic trust; not an additional explicit Lean binder. | same family and guards |
| L192 | T | external | deployment only | Retained release/tool/runtime/cryptographic trust; not an additional explicit Lean binder. | same family and guards |
| L193 | T | external | deployment only | Retained release/tool/runtime/cryptographic trust; not an additional explicit Lean binder. | same family and guards |
| L194 | T | external | deployment only | Retained release/tool/runtime/cryptographic trust; not an additional explicit Lean binder. | same family and guards |
| Rc5_T001 | T | external | actual antecedent | RuntimePersistence | same family and guards |
| Rc5_G001 | G | lead | actual antecedent | p.next t u | same family and guards |
| Rc5_G002 | G | lead | actual antecedent | e1 = observed entry t | same family and guards |
| Rc5_G003 | G | lead | actual antecedent | e2 = observed entry u | same family and guards |
| Rc5_G004 | G | lead | actual antecedent | same physical bank CP label | same family and guards |
| Rc5_G005 | G | lead | actual antecedent | same physical public CP key | same family and guards |
| Rc5_G006 | G | lead | actual antecedent | no intervening CP touch | same family and guards |
| Rc5_G007 | G | lead | actual antecedent | final parent TX1 status success | same family and guards |
| Rc5_G008 | G | lead | actual antecedent | recorded copy is original native saved vector | same family and guards |
| Rc5_G009 | G | lead | actual antecedent | recorded TX1 source action list | same family and guards |
| Rc5_G010 | G | lead | actual antecedent | state-threaded TX1 runtime actions and physical events | same family and guards |
| Rc5_G011 | G | lead | actual antecedent | state-threaded TX2 runtime actions and physical events | same family and guards |
| F3Y_G_L142 | P | session A | actual antecedent | source returned pair decodes to exact model dual-fold dot | same family and guards |
| F3Y_G_L143 | P | session A | actual antecedent | ∀ j : Fin 22, foldWord alpha0 (batchedWord W gamma) (q j) = V(q j) | same family and guards |
| F3Y_G_L144 | P | session A | actual antecedent | first semantic polynomial boundary equals claim; under SAME EquationEndpoint view/claim/polys parsing guards | same family and guards |
| F3Y_G_L145 | P | session A | actual antecedent | ∀ j : Fin 9, next boundary equals previous evaluation at challenge; under SAME EquationEndpoint view/claim/polys parsing guards | same family and guards |
| F3Y_G_L146 | P | session A | actual antecedent | last semantic evaluation equals exact masked spend terminal; under SAME EquationEndpoint view/claim/polys parsing guards | same family and guards |

## Non-vacuity and remaining gates

`ARX_Nonvacuity.conditional` (freshly printed and standard-axiom audited) derives an accepted admitted RunView with exactly JFx_NativeBytes proof/public bytes, conditional on a SAME installed native SupportedEntry and consistent native/H cylinder. It does not construct that pair or jointly inhabit all root premises. Rc10_Nonvacuity.composed and Rc10_Clean.exists_world are retained evidence, not new full ARX release fixtures. Exact partial fixture predecessors and the still missing full accepted pair are listed in ../account-rejoin9-20261026/ARX_ROOT_COMPARISON.md. No new proof round or fictional fixture premise is introduced by this audit.

Remaining actual P: native L142–L146, global F3Y_G_L142–L146 (session A), L154 (external query budget). Deployment P: L166 (native/source Result and ordered effects, including rejected prefixes), L187 (coherent release replay), L188 (final artifact/trust/dependency audit). Owner adoption and the full joint real-byte native pair remain open. The source-to-ELF release claim is not inferred from focused cached printing.

## Validation and scope

3/20 Lean attempts, both exit 0; 0/0 Kani. Wall 8.200638087 s total; maximum RSS 5558572 KiB; swaps 0. One own capped scope at a time; MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64, -j1 -M7000. Complete commands/revision/source and dependency hashes, resource and axioms receipts: Rc11_attempts.jsonl and Rc11_00*/. Both roots and the printed ARX consumers use only propext, Classical.choice, Quot.sound. No new theorem, dependency build, package replay, Rust/Kani/SBF run or shipped/cfg(kani) change. Unchanged cached objects and historical ELF pins were reused; no fresh ELF rebuild is claimed. No adoption, push, authoritative ledger edit or security-contract edit occurred. The separately requested amendment is a draft only.

The separate Rc11_003 boundary print unfolds the admitted mean, charge, query agreement, old binding, failure functional and exact constants. It also confirms L081 is STILL the global `P1Realization` at the fixed native root in both statements (`∀ bytes, sha256 bytes = H bytes`); RuntimeSyscall is success-conditioned. The new account coverage theorem uses query-restricted agreement and does not require that global equality for every consistent world. The retained global fixed-root antecedent has not been discharged or silently weakened by this recount.
