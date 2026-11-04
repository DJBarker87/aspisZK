from pathlib import Path
import json
E=Path(__file__).resolve().parent;Q=E.parent/'slice-d-define-20261104'
closed=json.loads((E/'NFT_CLOSED.json').read_text());done={f['function']for f in closed['functions']}
head='''# NFT field-helper bridges

**11 functions / 12 new Slice D rows CLOSED under NDT/NFK semantics through unchanged NFQ/NFK validators with stricter additive NFT gates.** Baseline NFQ D21/343 CLOSED becomes D33/343 CLOSED, 310 OPEN. Whole ledger:252 CLOSED,2 QUALIFIED,333 OPEN. The driver remains OPEN; the 100-bit per-attempt target is not yet established.

'''
head+='| Function | New CLOSED rows | Native / matched control | Complete model root |\n|---|---|---|---|\n'
for f in closed['functions']:
 head+='| '+f['function'].split('src/')[-1]+' | '+', '.join(f['rows'])+' | '+f['native_positive']+'/'+f['matched_control']+' | '+f['lean_root']+' |\n'
head+='''
Every entry has its own caller certificate, same-input child-domain proofs and complete Result/output/frame association. Exact receiver resolution excludes only spurious union-carrier alternatives; every selected internal edge is CLOSED. Details and packet provenance are in NFT_CLOSED.json, NFT_EDGES.json and NFT_CERTIFICATES.json. Each candidate retains frozen body hashes, support hashes and NFK semantic seals. No unrelated status changes are admitted.

The dot row covers the adopted Slice D seven-row internal-pair caller, not arbitrary other callers. Frozen state_only_poseidon.rs:530 constructs ROWS=[2,3,4,5,6,7,8] and maps the same weights/constants before its two calls. K076/077 prove the selected same-window read and term, K063/064 arbitrary-prestate term, K065/066 reducer fold, K070/073 fixed7 control; existing coherent FIq term/outer-loop induction and full7 theorem are reused in NFT_DotSource.source. K069's generic5..80 control timeout is excluded. Generic out-of-D lengths require their own packets.

The prepared3 row composes exact frozen right-cache prefix, native27-cut control, arbitrary-prestate selected product cell and all-other-cell frame with the actual emitted runStep and loop induction. PreparedFor and the CLOSED constructor's output-domain law establish canonical cache words. The final converter is newly CLOSED here. The generic accumulation helper and small2/3/4 path remain OPEN; this prepared function does not call them.

require_zero now has the matched pointer control missing from NFQ. Native arbitrary windows in completely arbitrary4096-byte backing prove pointer, Result/tag, length and immutable frame separately. Symbolic padding/suffix laws preserve the same allocation/input at every index; NFT_ZeroJoin.source_and_frame joins these to NFQ's finite-loop source theorem. The actual owned caller checks S2 checkpoint_size=1768 before borrowing and invokes require_zero on that same checkpoint view. The approved SDK same-view law remains explicit trust.

Field products use local opaque call logs and named Lean value laws in LPh_STUBS.md; no variable field product was proved by Kani. KMX is exactly the prescribed bcdf749b… patch, with shape-matched failing copy controls in the same source/configuration. No writable static, callback/function-pointer quarantine credit, or stub_verified is used in these new packets. Byte writers use complete value and disjoint arbitrary-prestate guard-window frame proofs; short packer uses explicit zero initializer, generic prefix law, full padded graph and all4 raw coordinate laws.

E002/E003 safe references use NCO extraction pins and unchanged generated outputs. L021 audits the initial12 roots; L060 audits58 additional roots using the byte-identical NEP walker. Both binaries pass all8 planted/mutation controls. Raw walks equal collectAxioms, with only propext/Classical.choice/Quot.sound. L058 imports the coherent deployed headline and prints standard axioms. Per-target exact exit/wall/RSS/swap/revision/axioms are in NFT_RESULTS.json and original receipts. No unchanged full regression was repeated.

NFT_certify.py checks the hash-pinned NFQ composed baseline and invokes unchanged NFK certificate_checks/materialize_recipe/row_checks/admit. It adds frozen-lock/offline/source/features, exact KMX/matched controls, all copied source/config pairs, source erasure, current successful model-source hashes, raw graph hashes/axioms and same-call child-domain gates. NFT_TESTS.json records72 recipe mutations; supplemental validator mutations are separate. NFQ and NFK source hashes are recorded, not rewritten.

Trust is retained/reclassified: P6/D188 NativeContractSemanticTransport optionA, root physical carriers/ABI/unique borrows, compiler/library/Aeneas/source-to-ELF and SDK view transport; RuntimePersistence, RuntimeReturnData and RuntimeMemcmp remain accepted runtime rows, and runtime digest=H realization remains explicit. L154 remains a statement parameter, D188 narrowed, headline AspisR1.RPx_Deployed.deployed. No premise retired, no security/privacy/two-transaction metric change.

All100 Kani,60 Lean/support,3 extraction slots are used. K005/K069 timeouts and K056 pre-CBMC compiler failure earn no credit; E001/L009 and L015 native-axiom draft are excluded. No cap/timeout increase or unchanged timeout rerun. Own scratch changes are supplied in NFT_HARNESSES.patch, with per-attempt pinned snapshots. Repository crates/programs and all shipped files remain unchanged; inherited ELF pins remain applicable. No key action, deployment, push or other worker edit.
'''
(E/'NFT_BRIDGES.md').write_text(head)
reasons={
'qm31_accumulate_product_channels':'''K024/025 cache prefix, K026/027 fixed9 control, K028/029 arbitrary-prestate selected product/frame and K030..033 copy controls passed. NFT_ChannelModel proves product/addition bounds and finite pointwise9-cell composition. Missing: an exact emitted/cohort definition for THIS generic helper and source-step/native association, with full cache/model invariant. L057 confirms the selected Probe/FIq environments contain no helper definition. A generic Nat trace theorem is not that association. Next: create/extract a prefix-owned helper model, prove its actual 9-cell/frame and cache association, audit, then compose. No native rerun is currently required for these existing shapes; a newly different shape would need fresh controlled Kani budget.''',
'qm31_sum_products_small':'''K084/085 (N2), K086/087 (N3), K088/089 (N4) controlled exact data-independent outer while chronology. Its actual child qm31_accumulate_product_channels remains OPEN. Missing: same emitted/cohort small-helper model, initial-zero/arity invariant, exact child/result/final-converter association and full-loop induction. L057 confirms no selected Probe/FIq small-helper definition. NFT_ChannelFour.generated_step and NFT_FieldFrontier.four_fit discharge the extra fourth-product arithmetic bound, but close no source row. Next: Lean/source association first; native support remains available for these scopes.''',
'qm31_sum_products2':'''K078/079 wrapper log proves exact two input arrays and arbitrary child reply in the original frozen one-call body. OPEN because the actual qm31_sum_products_small child and same model/caller join are OPEN. After the child closes, prove this wrapper's exact domain/model association and audit. A wrapper log alone earns no row; any new native shape needs new budget.''',
'qm31_sum_products3':'''K080/081 wrapper log proves exact three input arrays and arbitrary child reply. OPEN because qm31_sum_products_small and the complete same-input wrapper model association are OPEN. Proceed after that real dependency; the independent prepared3 path is already CLOSED. Native caller support exists; no multiplication in Kani.''',
'qm31_sum_products4':'''K082/083 wrapper log proves exact four input arrays and arbitrary child reply. OPEN because qm31_sum_products_small and full same-input wrapper association are OPEN. The prior three-product accumulator lemma had an insufficient 2*(P-1)^2 pre-cell bound for a fourth product: NFT_ChannelFour now proves3*(P-1)^2 and total4 products fitU64, but helper/source association still remains. Native wrapper and N4 control support exist.''',
'WideExact::square':'''K098/099 prove the four-site opaque QM mul/square/mul_u caller result log with complete canonical local replies; K100 corrupts a recorded argument in the identical source and fails its intended assertion. This is support, not CLOSED. Missing: each emitted callee's exact full-value law on the same canonical domain, the complete coherent WideExact square/source equation and field-product substitution/frame/representation join. Existing real QM add calls execute. Next work is Lean-only pairing/model association; no Kani field multiplication. If additional physical/interface facts arise, they need new controlled native budget.'''}
remaining=[]
for f in json.loads((Q/'NFQ_REMAINING.json').read_text())['functions']:
 name=f['function'];path=name.split('::')[0]
 if name in done or path not in ['crates/aspis-core/src/field.rs','crates/aspis-core/src/field/wide_exact.rs','crates/aspis-core/src/r0/scalar.rs']:continue
 key=name.split('src/')[-1].split('.rs::')[-1]
 assert key in reasons,key
 remaining.append((name,f['rows'],reasons[key]))
assert len(remaining)==6
text='''# NFT remaining obligations

Budget exhausted:100/100 Kani,60/60 Lean/support,3/3 extraction. No early stop. 11 functions/12 new D rows CLOSED; inherited D33 CLOSED/310 OPEN. Every unclaimed row and the deployed driver remain OPEN. These are exact proof gaps, not counterexamples to the target.

'''
for name,rows,reason in remaining:text+='## '+name+'\n\nRows: '+', '.join(rows)+'. '+reason+'\n\n'
text+='''## Upward callers and slice boundaries

PreparedQm31Multiplier::new was already CLOSED by NFQ; its canonical cache output-domain law is reused. Prepared3 users may now cite the new caller certificate, but none closes automatically. Other Prepared users and arithmetic-prelude callers still require their own frozen native packet, complete same-input model join, actual child domains and ax2 audit. All proof-run budgets are exhausted, so no such new gate was launched. The additive ledger deliberately keeps every other status unchanged.

TX2:046's unresolved CodeField::from_m31 resolves to <WideExact as CodeField>::from_m31 at frozen r0/scalar.rs:89, body90 (impl87–91), through the canonicalizing M31 trait embedding. NFT_FROM_M31_FINDING.md records exact source SHA and nested targets; inventory unchanged. Generic other qm31_m31_dot callers are outside this claimed seven-row SliceD occurrence and need explicit domain packets. Never infer global arbitrary-length closure.

Use the retained private cache/export and pinned coherent SInt2/Aeneas objects. Do not rerun K005's mutable-slice contract or K069's generic5..80 control unchanged, raise caps, prove multiplication in Kani, import legacy S1/old-FIo, or treat unvalidated horizontal WIP as closure. Native exhaustion is not a reason to abandon the Lean gaps above in a newly budgeted job; this job also exhausted every Lean slot.
'''
(E/'NFT_REMAINING.md').write_text(text)
handoff='''# NFT final handoff

Branch codex/cx-slice-d-field-20261104. **11 functions /12 new D rows CLOSED**, driver OPEN. D33 CLOSED/310 OPEN; whole ledger252 CLOSED/2 QUALIFIED/333 OPEN. Target100-bit per-attempt soundness not yet established. NFT_BRIDGES.md explains the certificates; NFT_REMAINING.md lists each of the6 remaining field-family members and exact next obligation. No other row changes.

All budget used:100 Kani,60 Lean/support,3 extraction. NFT_BUDGET.json and NFT_RESULTS.json reconcile all163 unique attempts, including rejected drafts; original full receipts and source pins remain in NFT_ATTEMPTS.jsonl and per-attempt directories. Every launch had reservation exit0 AND allowed:true, capsHigh6G/Max8G/Swap0/Tasks64, optimized Rust and Lean-M7000. Zero swap; highest recorded child RSS6354500KiB (excluded K005 timeout), final audit5708408KiB. Caps were never raised; no unchanged timeout retry.

L021's12 roots plus L060's58 new roots pass unchanged-walker raw/collect equality with standard axioms and all8 fixtures. L058 coherently imports AspisR1.RPx_Deployed.deployed and prints standard axioms. L015's bv_decide native axioms are excluded. Frozen graph/offline/lock-before-after validation accompanies EVERY Kani attempt, including failures. KMX copy patchbcdf749b… and same-configuration negative controls are mandatory for admitted copy-dependent packets; argument/call logs are local records. Field products are discharged only in Lean (LPh_STUBS.md).

Validation:python3 evidence/slice-d-field-20261104/NFT_certify.py; then NFT_tests.py and NFT_validator_tests.py. The additive validator imports unchanged NFQ/NFK helpers, starts from the hash-checked NFQ ledger, checks selected actual child domains and admits only these12 rows. Frozen baselines/other workers are never written. Review NFT_CLOSED.json, NFT_EDGES.json, NFT_LEDGER_DELTA.json, NFT_AUDIT.json and NFT_CERTIFICATES.json. No CLOSED callee alone closes its caller.

Host dombarker@100.108.41.90. Retained own workspace /home/dombarker/project-offloads/codex-cx-slice-d-field-20261104; retained own cache /home/dombarker/project-offloads/codex-cx-slice-d-field-cache-20261104; export NFT_exports_20261104. NFT_CACHE_END.json pins35 copied own objects, records removal of only private rebuildable Rust targets and empty own TMPDIR. NFT_CACHE_IMPORTS.json.xz plus raw SHA pins208086 copied baseline files; NFT_CACHE_RESTORED.json verifies all31 NFQ exports. Reuse exact ordered LEAN_PATH and pinned Aeneas objects from receipts; no shared cache was edited/deleted.

All source changes live as external-scratch harness patch/receipts under this evidence prefix. NFT_HARNESSES.patch and SHA are the final patch; per-attempt snapshots preserve earlier inputs via content-addressed symlinks. No shipped/research crate/program file changed; inherited ELF hashes:default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4; devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299; Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548. No rebuild triggered, key/account action, deployment or push.

Retain P6/D188 optionA transport as trust reclassification, root physical ABI/borrow and compiler/library/Aeneas/source-to-ELF, SDK same-view transport, accepted RuntimePersistence/RuntimeReturnData/RuntimeMemcmp, digest=H realization. Headline remains RPx_Deployed.deployed; L154 is a statement parameter; D188 narrowed. No change to per-attempt100-bit metric, privacy or two-transaction design. TX2:046 trait-dispatch finding is documented; inventory and sibling worktrees are untouched.
'''
(E/'NFT_HANDOFF.md').write_text(handoff)
