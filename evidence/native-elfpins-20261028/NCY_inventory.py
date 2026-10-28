from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).parent
raw=subprocess.check_output(['git','show','HEAD:evidence/l188-audit1-20261027/L8a_TrustFieldMap.json'])
fields=json.loads(raw)
header='''# NCY final release trust inventory draft — 2026-10-28

For the final **L188 audit**, the headline is `AspisR1.RPx_Deployed.deployed`
with installed frozen3 configuration. **Target not yet established.** This single
table inventories named fields and external boundaries; it does not invent a
trust item per use or silently recount inherited 83T/89T. Repeated uses share
records/worlds exactly as the kernel statement specifies. Allocation interfaces,
historical derived records and game conditions are labelled to avoid counting
them as independent assumptions.

Authority: binding SECURITY-CONTRACT-20261021.md amendments 2026-10-26 through
2026-10-28 (fifth), C3-BIN dated rulings, and the owner-approved
TRUST-INVENTORY-APPENDIX-DRAFT-20261027.md. Exact field types/quantifiers are in
`evidence/l188-audit1-20261027/L8a_structure.json` and L8a_008/stdout.log;
these are reused predecessor evidence, not a fresh RPx field census.
The complete RPx kernel statement and root audit are in
`evidence/replay-deployed2-20261027/RPx_Deployed.kernel.lean.txt`, RPx_0038/0039.
The field-map input is pinned in NCY_INVENTORY_INPUTS.json.

For all SDK rows below, laws are only under the exact `L.related`, `Valid`,
counter/enabledness/lifetime conditions printed in L8a_008 and preserve reply
AND next heap. SDK pin is solana-account-info 2.3.0 / frozen production lock.
Excluded throughout: Ref clone/map_split/leak, realloc, Rc clone/free, lamport
borrows, CPI, reentrancy and concurrency. No SDK row supplies caller success,
proof bytes, output, oracle history or a child/source join.

| Field / boundary | Exact retained scope | Authority / evidence | Classification / final-audit qualification |
|---|---|---|---|
'''
sdk={
'account_data_cell':'Typed AccountInfo data-cell association with its related abstract account cell.',
'cell_payload':'Related data-cell payload/carrier interpretation.',
'cell_counter':'Related RefCell borrow-counter interpretation.',
'shared_ok':'Successful enabled shared data borrow: returned guard and next heap match.',
'shared_err':'Conflicting shared data borrow: error and heap match.',
'exclusive_ok':'Successful enabled exclusive data borrow: returned guard and next heap match.',
'exclusive_err':'Conflicting exclusive data borrow: error and heap match.',
'shared_deref':'Live shared guard dereference gives its cell payload.',
'exclusive_deref':'Live exclusive guard dereference gives its cell payload.',
'guard_move':'Moving a live guard preserves its identity, provenance and ownership relation.',
'shared_drop':'Dropping a live shared guard restores the specified shared counter and frame.',
'exclusive_drop':'Dropping a live exclusive guard restores the specified exclusive counter and frame.',
'error_move_drop':'Move/drop interpretation of borrow-error outcomes with specified frame.',
'borrow_frame':'Borrow operations preserve every heap region outside their specified cell effects.',
'guard_liveness':'Validity/liveness association for tracked guards at each permitted use.'}
entry={
'valid':'Initial valid typed/abstract heap relation.',
'freshGuards':'Fresh tracked guard state at entry.',
'noExternalBorrows':'No untracked external data borrows at entry.',
'liveAccount':'Every admitted account is live at entry.',
'counterZero':'Admitted data-borrow counters are initially zero.',
'duplicateKeysShareCell':'Equal admitted keys share the same abstract cell.',
'sharedCellsOnlyEqualKeys':'Shared abstract cells imply equal admitted keys.',
'entry':'Nested admitted entry record, for the actual TX1 three-account / TX2 seven-account entries.',
'related':'Actual entry world is related to the SAME abstract entry heap.'}
rows=[]
for f in sorted(fields,key=lambda f:f['field']):
 name=f['field'];last=name.rsplit('.',1)[-1];item=f['item'];scope=f['scope'];status='Retained approved scope; exact kernel guards apply.'
 if 'S2TrustedSdkBorrow.' in name:scope=sdk[last];status='T: route-B field; no caller/source discharge.'
 elif 'RuntimeEntrypointAdmission.' in name:scope=entry[last];status='T: initial admission only; no post-state, persistence, allocator success or acceptance.'
 elif 'Allocator.' in name:scope={'allocate':'Private-state data operation `A → Nat → Result A`.','cleanup':'Private-state data operation `A → Result A`.'}[last];status='Data interface, not a Prop guaranteeing success or permission to write accounts; runtime association remains explicit.'
 elif 'S2W_DigestExtraction.AeneasExtraction.' in name:
  scope={'stage1':'For all program/accounts/data, native1 equals the installed owned stage1 under the SAME ops.','stage2':'For all program/accounts/data/slot (including inner clock Err), native2 equals the installed owned stage2 under the SAME ops.','digestSource':'For all self/parts, installed ops.op43 equals the SolanaDigest wrapper around the SAME hashv; outer Result preserved.'}[last]
  status='T: narrowed D188 trace fidelity or accepted direct P6 bridge plus amendment-five semantic transport. No unverified opaque-body/iterator-write credit.'
 elif 'S2W_ExtractionBoundary.AeneasExtraction.' in name:status='Derived older interface via S2W_DigestExtraction.sourceBoundary; no extra independent trust.'
 elif 'CheckpointVersionBinding.' in name:status='Historical conditional interface ONLY; not free new trust. Actual history comes from data persistence + approved game + source proofs.'
 elif name.endswith('P1.realization'):scope='For every byte string, sha256 bytes = H bytes. Ideal-oracle realization, not a theorem that physical SHA is random.';status='T: P1, separate from runtime reply and native wrapper association.'
 elif name.endswith('RuntimeSyscall.returningValue'):scope='hashv parts = ok digest implies decodeState digest = sha256(flatten parts), on identical slices; no totality or termination.';status='T: returning syscall value only. Native bridge proves arguments/reply unchanged; never unwinds SHA.'
 elif last=='slice_copy_from_slice':scope='copy s dst src = specification s dst src; equal lengths replace only destination payload contents; unequal lengths panic.';status='T with W1: total abstract extension is not invalid-reference native semantics; every use proves valid admitted references. Kani copy fidelity separately constrained below.'
 elif last=='option_ok_or':scope='For every x,e, installed ops.op0 x e = Port1_LibrarySource.okOr x e.';status='Deployment T L192: pure Option/Result only; not Option<fn> native-credit permission.'
 elif last=='result_unwrap32':scope='For every x, installed unwrap32 x equals emitted unwrap32 x, including fail/panic.';status='Deployment T L193: pure Result semantics; no ownership/frame proof.'
 rows.append((f'`{name}`',scope,f['acceptance']+'; approved inventory first 2026-10-27 amendment',status))
extra=[
('RuntimePersistence / CPR_DataPersistence.TwoTransactionLaw','For next t,u on the same bank lineage and each ordinary key: loaded u = visible(tentative t if parent success, else before t); zero lamports means absent. Ordinary excludes fee payer/durable nonce. DATA BYTES ONLY.','Contract 2026-10-26 §3; L8a_008; RUNTIME-PERSISTENCE-ITEM-20261026.md','T: no owner, balance, privilege, SDK or verifier guarantee; older full-image CPR_Persistence candidate unadopted.'),
('D188 operational trace scope and exclusions','SAME associated body/input/digest replies/source-producer pins preserve accepted Result and chronological attempted digest calls, duplicates and rejected prefixes. Both reject; exact non-Ok error kinds may differ.','Contract first/second/third amendments; BEn_ExtractedTrace.native; D188-PROVENANCE-FINDING-20261027.md','Retained trust, narrowed: low_base_p_digits dropped write has no credit; mutable iterator/accessor writes require static scan plus write-sensitive native differential. A0-A8 are waived only for actually bridged functions; otherwise unresolved association obligations.'),
('Native contract semantic transport (result projection)','ONLY frozen owned TX1 stage1, owned TX2 stage2 and SolanaDigest bodies/references/dictionaries/features/input-outcome encodings/tool versions enumerated by accepted receipts: Kani/CBMC Rust and pinned Charon/Aeneas reference denote the same primitive semantics under certified common external world. Explicit associations native1/native2, digest wrapper ops.op43, external hashv.','Contract 2026-10-28 fifth; appendix clarification; evidence/native-topspec-20261028/NCQ_TOPSPEC.md','EXPLICIT CLARIFICATION of existing P6/D188, not new kind of trust. Every use is RECLASSIFICATION of extraction, never a premise removal by proof. Draft contracts alone are not accepted certificates; result projection alone supplies no ordered effect equality.'),
('P6 Kani/CBMC tool fidelity — L190','Pinned cargo-kani 0.67.0 frontend/MIR/codegen/CBMC/solver correctly certify the exact native/reference property and domains in accepted receipts, with frozen dependency graph, offline lock hash invariance, deployed features/profile/body parity.','Contract amendments third/fourth; C3-BIN shared P6 method and rulings (r\u2032),(t),(u); NCR_FEATURE_TABLE.md','Retained external tool trust, not a Lean P6 axiom or an arbitrary source refinement. K-2 function-pointer/Option<fn>-dependent passes QUARANTINED. No NCY Kani run.'),
('Kani copy and contract fidelity restrictions (within P6)','Copy-dependent credit ONLY exact KMX_copy_stubs.patch SHA bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67 plus matching negative-control FAIL in same config. Every proof_for_contract and stub_verified has matched failing control; non-Bool/record shapes additionally pass three fidelity controls.','Contract fourth; KANI-FIDELITY-FINDING-20261028.md; C3-BIN (r\u2032)/(t)/(u)','Narrows existing P6. Inverted ensures fails, unimplied caller assertion fails under stub_verified but passes real body, modifies violation detected. Timeouts give no credit; no custom copy stubs. Field multiplies use paired Lean value/ok theorem and caller-proved canonical domain; loops use one native iteration + Lean induction + step association.'),
('P7 SBF compiler/LLVM/linker semantics — L189','Pinned Rust→LLVM→SBPF platform-tools compiler/linker preserves selected source observations for exact frozen source revision 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387, features/profile/ABI/build IDs, and all three pinned ELFs.','evidence/lowering2-20261026/Low2_source_to_elf_manifest.json and Low2_final_receipt.json; NCR_SOURCE_TO_ELF.md; NCY_ELF_REPRODUCTIONS.md','RETAINED SBF-COMPILER SEMANTICS TRUST. Bit-exact hashes retire artifact association under P7, not compiler correctness. No live loaded-program/upgrade-authority/readback claim. Stack-offset diagnostics retained for S10 review.'),
('Pinned Lean/Mathlib/Aeneas implementation base and kernel','Exact selected Lean 4.32.0/toolchain/lake/library objects, Aeneas safe Vec/Box models and source-to-object pins resolved by ordered paths in coherent RPx/SInt2 cohort; checked logical values distinguished from runtime implementations.','RPx seals/retained-object-pins; SInt2 final-closure manifest; approved appendix library-surface inventory','P7/D188 library-base reuse, not fresh library replay or arbitrary external-template acceptance. Final audit must join exact objects; no NCY Lean launch or library modification.'),
('Standard logical base','Only propext, Classical.choice, Quot.sound in each audited top proof dependency.','RPx_0038 root audit; RPx_0039 all 105 fresh declarations; r1p-common §3/local-lean §4','Accepted logical axioms, distinct from runtime/security hypotheses. 180 formatter records root-unreachable is not strict import-wide standard-only; F-AXIOM remains a final audit finding, not new accepted axioms.'),
('Runtime/loader/ABI/rollback envelope — L191','Actual entries, private allocation/abort/rollback, runtime invocation and loaded-program/source association on admitted executions, only documented pinned interfaces; data persistence and returning digest laws remain separately scoped.','C3-BIN 2026-10-23 02:40/11:05/18:05, 2026-10-26 Vec/Box ruling; TRUST-AUDIT release table','Retained deployment runtime boundary. Does not manufacture concrete heap validity, CPI authority, arbitrary history, syscall totality or safe unproved raw writes. S10 completeness/association still audited.'),
('Cryptographic/security model — L194','Adopted frozen3 account-recorder two-transaction failure game with charged collision alternative and exact query losses/constants. At least 100-bit classical PER-ATTEMPT target; no work-normalised or grinding credit; privacy and two-transaction design preserved.','Binding SECURITY-CONTRACT-20261021.md including amendments; RPx exact kernel statement','Retained contract/model assumptions, no new cryptographic premise invented to cover source gaps. Numeric model bounds do not alone establish deployed security; P1 realization is separate.'),
('Game a–d, successful-wrapper conditioning, and L154','Same adjacent bank-lineage TX1/TX2, same physical checkpoint key, no intervening touch, successful parent, ordinary nonzero relevant account, same entries; success antecedents retained. L154 issued-query bound (duplicates/rejected prefixes counted) is Q parameter.','Contract 2026-10-26 §2 and second 2026-10-27 amendment; RPx statement','G / STATEMENT PARAMETER, not external trust and not a proved query-budget discharge. Preserve exact 11 expanded game clauses + 2 wrapper antecedents. Joint real-byte non-vacuity still required.'),
('Unadopted / open surfaces (not trust)','FixturePdaRuntime DEFERRED; historical full-account persistence, arbitrary unsafe source equivalence, incomplete native caller domains/trace joins, D188-P2 cross-path gaps and import-only nonstandard axioms have no blanket trust credit.','Contract fifth; appendix W1/D188-P2/F-AXIOM; RPx formatter records; NCY_DEPLOYMENT_ROWS.md','Do not count these as approved trust or silently erase them. Direct bridges close only their actual domains; a stronger-than-caller precondition is a finding. Final L188 must resolve or explicitly classify each residual.')]
rows+=extra
text=header+'\n'.join('| '+' | '.join(row)+' |' for row in rows)+'\n\n'
text+='''No new trust or premise removal is claimed by this draft. The final auditor must
reconcile this named-boundary table with the exact expanded RPx and accepted
native receipt closure, including every source/feature/domain and retained finding.
The older L8a import census (105 nonstandard axiom names) is historical evidence;
RPx root-unreachability is scoped to its sealed cohort, not a claim that every
imported declaration is standard-only. E1/E2 prover entropy/privacy assumptions
are separate from this soundness headline; this lane changes neither their
scope nor the privacy release gates.

Validation: 0 Lean, 0 Kani; no new theorem, #print axioms N/A. Reused root
axiom evidence is exactly the standard three above. No full manifest replay.
'''
(E/'NCY_TRUST_INVENTORY_DRAFT.md').write_text(text)
(E/'NCY_INVENTORY_INPUTS.json').write_text(json.dumps({'field_map_git_path':'evidence/l188-audit1-20261027/L8a_TrustFieldMap.json','field_map_sha256':hashlib.sha256(raw).hexdigest(),'field_rows':len(fields),'external_or_classification_rows':len(extra)},indent=2)+'\n')
