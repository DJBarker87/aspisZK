"""Render the audited premise families; does not invoke a prover or build tools."""
from pathlib import Path
from collections import Counter
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'evidence/premise-ledger-20261025'
BASE = 'docs/research/100bit-spend-path-20261013/lean/'
rows = []


def add(group, name, definition, meaning, cls='P', owner='lead', job='S2 lead; no completed removal', evidence='Ledger_003/stdout.log'):
    rows.append(dict(id=f'L{len(rows)+1:03}', group=group, name=name,
                     definition=definition, meaning=meaning, classification=cls,
                     owner=owner, job=job, evidence=evidence))


sdk = BASE + 'S2TrustedSdkBorrow.lean'
for field, parts in {
    'account_data_cell': ['data-cell identity', 'lamports-cell identity', 'shared data-cell alias agreement', 'live data/lamports separation'],
    'cell_payload': ['typed cell payload equality'],
    'cell_counter': ['counter equality', 'live-guard lookup equality'],
    'guard_liveness': ['live guard identity', 'allocation liveness', 'descriptor identity'],
}.items():
    for part in parts:
        add('A', 'sdk.'+field+'.'+part, sdk+'#'+field,
            'For related valid local states: '+part, 'T', 'external', 'Route B adopted; retained library trust')
for field in ['shared_ok','shared_err','exclusive_ok','exclusive_err','shared_deref','exclusive_deref.read','exclusive_deref.write','guard_move','shared_drop','exclusive_drop','error_move_drop','borrow_frame']:
    for part in ['reply', 'related']:
        add('A', 'sdk.'+field+'.Matches.'+part, sdk+'#'+field.split('.')[0],
            ('Exact typed transition and reply' if part == 'reply' else 'Successor library state relates to specified heap')+
            '; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained',
            'T', 'external', 'Route B adopted; retained library trust')
add('A','std.slice_copy_from_slice',BASE+'S2W_TrustedStd.lean#TrustedStd',
    'Copy equals the full slice-copy specification, including panic and frame', 'T','external','TrustedStd retained')

valid_parts = {
    'uniqueToken':'pairwise distinct live tokens', 'uniqueOwner':'pairwise distinct live owners',
    'counterLower':'minCounter ≤ counter', 'counterUpper':'counter ≤ maxCounter',
    'counterEquation':'counter = external + shared count − exclusive count',
    'exclusive.externalZero':'tracked exclusive implies external = 0',
    'exclusive.sharedZero':'tracked exclusive implies no tracked shared guard',
    'exclusive.one':'tracked exclusive implies exclusive count = 1',
    'externalNegative.sharedZero':'negative external implies shared count = 0',
    'externalNegative.exclusiveZero':'negative external implies exclusive count = 0',
    'guardAllocated':'each live guard has an allocated cell',
    'guardDescriptor':'each live guard descriptor equals the payload descriptor',
    'liveSeparate':'live account data and lamports cells differ',
    'liveAllocated':'live account data cell is allocated',
}
for tx in [1,2]:
    for part, meaning in valid_parts.items():
        add('A',f'admission{tx}.entry.valid.{part}',sdk+'#Valid',
            f'TX{tx} initial heap: '+meaning,'T','external','Runtime/entrypoint admission retained')
    for field,meaning in {
        'freshGuards':'no initial tracked guards', 'noExternalBorrows':'external counter is zero',
        'liveAccount':'all admitted account owners live', 'counterZero':'all admitted account counters zero',
        'sharedCellsOnlyEqualKeys':'shared data cell implies equal keys',
        'duplicateKeysShareCell':'equal keys imply shared data cell',
    }.items():
        add('A',f'admission{tx}.entry.{field}',BASE+'AdapterRwRuntimeAdmission.lean#RuntimeEntrypointAdmission',
            f'TX{tx}: '+meaning,'T','external','Runtime/entrypoint admission retained')
    add('A',f'admission{tx}.related',BASE+'S2W_D189Consolidation.lean#RuntimeEntrypointAdmission',
        f'TX{tx} concrete library state relates to entry heap','T','external','Runtime interpretation retained')
for field in ['stage1','stage2','digestSource']:
    add('A','extraction.'+field,BASE+'S2W_DigestExtraction.lean#AeneasExtraction',
        {'stage1':'Native TX1 function equals owned extracted stage1 at the exact installed dictionary',
         'stage2':'Native TX2 function equals owned extracted stage2 at the exact installed dictionary',
         'digestSource':'op43 equals the emitted digest wrapper around hashv'}[field],
        'T','external','D188 extraction association retained; source-instance pins still required')
add('A','p1',BASE+'S2Z_Oracle.lean#P1Realization','∀ bytes, sha256 bytes = H bytes, inside the ideal-oracle realization',
    'T','external','Security-contract ROM assumption; no deterministic random-function proof')
add('A','syscall',BASE+'S2Z_Oracle.lean#RuntimeSyscall','Every successful hashv decodes to sha256 of the exact flattened parts',
    'T','external','Runtime/syscall trust retained')
for tx in [1,2]:
    add('A',f'accepted{tx}',f'lean/Op4P_Accepted.lean#accepted{tx}; lean/Tx2I_Accepted.lean#accepted{tx}',
        f'TX{tx} wrapper returns the given inner Ok, post heap and allocator state; event restriction, not a universal-success obligation',
        'P','lead','Preserve as accepted-event antecedent; instantiate from actual run')
for field,meaning in {'hL':'34 + D ≤ N','encLen':'every encoded message has length ≤ D','decEnc':'decoder inverts encoder on messages'}.items():
    add('A','p.'+field,'docs/research/v8-fs-generic-20261006/lean/FS2/Duplex.lean#Params',
        meaning+'; unused p binder in these accepted-pair proofs, not an execution fact',
        'P','lead','No removal job; structural parameter law','Ledger_005/stdout.log')
add('A','port.erasure',BASE+'S2W_ExpandedChildren.lean#ChildConeJoin',
    'Every typed child execute result erases to invoke ops call, retaining Result failure/divergence behavior',
    'P','lead','Op5T_ batch/marks; S2 child interpreter integration')
add('A','firstMarks.source',BASE+'S2W_TraceSplice.lean#FirstMarks',
    'ALL events marked TX1 must have the complete firstTrace site layout, with no success guard',
    'C','lead','codex/cx-op5-tx2-20261025, Stage A','../op5-concrete-20261025/HANDOFF.md')
add('A','secondMarks.source',BASE+'S2W_TraceSplice.lean#SecondMarks',
    'ALL events marked TX2 must have the complete secondTrace layout, with no success guard; analogous rejected-prefix risk, no new contradiction proof here',
    'C','lead','codex/cx-op5-tx2-20261025; audit success conditioning','Ledger_003/stdout.log')

for field,meaning in {'header':'actual successful TX1 checkpoint decodes to both proof/public digests','size':'actual returned checkpoint has length 1768'}.items():
    add('B','writer.'+field,BASE+'S2W_AuthenticatedInputs.lean#CheckpointWriterConeJoin',meaning,
        job='codex/cx-tx1-query-20261025; Q2 writer connection')
add('B','reader.checkedHeader',BASE+'S2W_AuthenticatedInputs.lean#CheckpointReaderConeJoin',
    'Actual successful authenticated TX2 checks the same decoded two-digest checkpoint header',
    job='codex/cx-tx2-query-20261025; Q2 reader connection')
for field,meaning in {
    'savedAtCommit':'the SAME committed ledger key holds the actual post1 checkpoint bytes',
    'loadedAtEntry':'TX2 loaded bytes equal the final history value of that SAME key',
    'noInterveningWrite':'every history event is rollback or writes a different key',
}.items():
    add('B','history.'+field,BASE+'S2X_RuntimeRetention.lean#CheckpointVersionBinding',meaning,
        job='S2 lead / RowOrder_AcceptedPairHistory; concrete Pool history instance open')
for part in ['proof','pub']:
    add('B','p2prime.binding.'+part,BASE+'R9PoolRuntimeBinding.lean#P2Prime',
        f'For THIS writer/reader pair, both matching digests imply identical complete {part} bytes; not hash injectivity',
        job='S2 lead; protected-history or budgeted collision route, no completed discharge')
add('B','entry.parsed',BASE+'S2W_ChildJoins.lean#FirstEntryVerifierConeJoin',
    '∃ transcript and parsed proof, parseReached on these SAME proof bytes returns it',
    job='S2 lead; Op3I_/Op4P_ header/scan insufficient for full parser/transcript instance')
for batch in [0,1]:
    for part,meaning in {'start':'range starts at slotStart(3*b+k)','finish':'range ends at start + 32*capacity(3*b+k)','bound':'end is within actual proof','index':'actual checked source range returns nodes b k'}.items():
        add('B',f'multiproof.batch{batch}Ranges.PhysicalRange.{part}',BASE+'S2Y_OwnedChildren.lean#PhysicalRange',
            f'∀ k < 3, batch {batch}: '+meaning+'; SAME start/end witnesses across all four rows',
            job='codex/cx-op5-tx2-20261025')
for part,meaning in {'length':'actual proof length ≥ 7495','index':'checked [7031,7495) range returns the SAME y1'}.items():
    add('B','scan.scanArgument.'+part,BASE+'S2Y_OwnedChildren.lean#Y1Range',meaning,
        job='S2 lead; Op4P_ installed scan, internal y1 call connection remains')

for round_ in [0,1]:
    for field,meaning in {'field0':'offset-0 field read returns c0','field4':'offset-4 field read returns c4','add':'c0+c4 source primitive returns lhs','quarter_run':'quarter primitive returns quarter','multiply':'claim times quarter returns rhs','evaluate':'polynomial primitive returns value at exact alpha'}.items():
        add('C',f'r{round_}.{field}','lean/RowFinish_Control.lean#RoundValues',
            f'Round {round_}: '+meaning,'P','session A','S3/S4/S5/S9 primitive instances; FinT_ consumes unchanged')
for field,meaning in {
    's2':'actual prepared variant is S2','ha0':'actual alpha[0] read returns alpha0','ha1':'actual alpha[1] read returns alpha1',
    'hw':'newWeights returns the SAME weights','has':'alpha[..2] source slice returns alphas',
    'hp':'pair primitive returns the SAME pair','hd':'dot primitive on actual flushed weights returns dot',
    'hi':'stored-decision input on parsed/q/tr returns this i','hq':'selected transcript queries return this q',
    'read':'literal matching read on these typed rows returns i.data','decoded':'query bytes decode to the SAME q',
}.items():
    own='session A' if field in ['hw','hp','hd'] else 'lead'
    add('C',field,'lean/Tx2I_Accepted.lean#'+field,meaning,'P',own,
        'Session A primitive instance' if own=='session A' else 'Tx2Q_ and S2 same-witness model/transcript connection')
for round_ in [0,1]:
    for field,meaning in {'boundary':'decoded read/add result is the model polynomial boundary','quarter':'decoded multiply is quarter * decoded claim','eval':'decoded polynomial evaluation equals model evaluation'}.items():
        add('C',f'pairing_S3_S5_S9.round{round_}.{field}',BASE+'Port4D_Pairing.lean#RoundLaws',
            f'Round {round_}: '+meaning,'P','session A','S3/S4/S5/S9 laws retained')
for field,meaning in {'claim':'prepared claim decodes to JointFunctionalBinding.claimedValue',
                       'alpha0':'prepared alpha0 matches data.alpha0','alpha1':'prepared alpha1 matches data.alpha1',
                       'pair':'source returned pair decodes to exact model dual-fold dot'}.items():
    add('C','pairing_S3_S5_S9.'+field,BASE+'Port4D_Pairing.lean#PairingLaws',meaning,
        'P','session A','S3/S5/S9 instances retained')
add('C','matches_S4_S7',BASE+'MatchingSupport.lean#match0',
    '∀ j : Fin 22, foldWord alpha0 (batchedWord W gamma) (q j) = V(q j)',
    'P','session A','S4/S7 matching arithmetic instance')
for part,meaning in {'initial':'first semantic polynomial boundary equals claim','chain':'∀ j : Fin 9, next boundary equals previous evaluation at challenge','terminal':'last semantic evaluation equals exact masked spend terminal'}.items():
    add('C','semantic_S3_S9.EquationEndpoint.'+part,BASE+'R3SemanticEquationCore.lean#Equations',
        meaning+'; under SAME EquationEndpoint view/claim/polys parsing guards',
        'P','session A','S3/S9 semantic equation instances retained')
add('C','dot_S5','lean/Tx2I_Accepted.lean#dot_S5',
    'Decoded dot equals sum over all64 model final values and actual accumulator weights',
    'P','session A','S5 actual operand instance')
add('C','canonical_S3_S4_S5_S9','lean/Tx2I_Accepted.lean#canonical_S3_S4_S5_S9',
    'sourceE(ofE x)=x for all eight listed round/pair/dot/rhs operands',
    'P','session A','S3/S4/S5/S9 canonicality on actual operands')
add('C','saved_ten','lean/Tx2I_Accepted.lean#saved_ten',
    'Actual op18 resumed accumulator equals model write(model i.data rho q).accumulator',
    job='codex/cx-tx2-query-20261025; still open', evidence='../tx2-query-20261025/HANDOFF.md')
add('C','twelve','lean/Tx2I_Accepted.lean#twelve',
    'Actual op6 return with op9 flushed/back-materialized weights equals twelve model steps from SAME resumed accumulator',
    job='codex/cx-tx2-query-20261025; still open', evidence='../tx2-query-20261025/HANDOFF.md')
for field,meaning in {
    'map_add':'each model F j and F0 preserves addition',
    'map_smul':'each model F j and F0 preserves scalar multiplication',
}.items():
    add('C','i.data.Functional.'+field,BASE+'MatchingSupport.lean#Functional',
        meaning+'; structural LinearMap law, already supplied by its model type, not a native-source discharge',
        'P','lead','Model well-formedness; no removal job','Ledger_007/stdout.log')
add('C','tr.statement.initFits',BASE+'R1UnifiedSamplerPublic.lean#Public',
    '75 + pubBytes.length ≤ address bound; named proof field of model public carrier, supplied by its type; physical public association remains open',
    'P','lead','Model well-formedness; source bound association in StoredCarrierBinding','Ledger_007/stdout.log')

add('D','hqueries',BASE+'OraclePortHeadlineFrozen2PerAttempt.lean#final_soundness',
    '∀ ideal H, prover-issued log length ≤ Q; budget condition on the adversary, repeats counted',
    'P','external','Preserve as quantified query-budget condition', 'Ledger_004/stdout.log')
add('D','globalJoin.verifier',BASE+'OraclePortFrozen2Join.lean#AcceptedVerifierJoin',
    '∀ H and arbitrary logical Input, source acceptance implies exact eval log+Bool equality; independent logical proof can disagree with physical bytes',
    'C','lead','Port1 canonical carrier corrects domain; original theorem remains conditional',
    '../ports1-20261023/STAGE4.md')
add('D','globalJoin.annotated',BASE+'OraclePortFrozen2Join.lean#AcceptedRunJoin',
    'For every arbitrary-Input Prover and H, accepted annotated source equals full frozen2 annotated experiment',
    'P','lead','S2 lead; domain correction and per-attempt endpoint composition open','Ledger_004/stdout.log')
add('D','canonicalJoin.verifier',BASE+'Port1_CanonicalJoin.lean#AcceptedVerifierJoin',
    '∀ byte Submission and H, accepted physical source equals frozen2 eval on input(submission), including ordered oracle answers',
    'P','lead','S2 lead; raw frozen2/source interpretation still open','Ledger_004/stdout.log')
add('D','canonicalJoin.annotated',BASE+'Port1_CanonicalJoin.lean#AcceptedRunJoin',
    '∀ P whose outputs are Carried in each H, accepted two-pass annotated eval equals frozen2 eval',
    'P','lead','Port1_CanonicalJoin.two_pass reduces to physical + raw join; raw instance open','Ledger_004/stdout.log')
add('D','StoredCarrierBinding',BASE+'OraclePortRuntimeBindingC7.lean#StoredCarrierBinding',
    '∀ H and accepted runtime run, the ENTIRE run equals annotatedWith D rust (canon P); canonical headline substitutes lift P',
    'P','lead','S2 lead concrete deployment/history/experiment binding; runtime axioms alone insufficient','Ledger_004/stdout.log')
add('D','Physical rust (transport predecessor)',BASE+'Port1_StoredCarrier.lean#Physical',
    'Equal publicBytes and stored bytes imply identical source oracle Programs; driver_physical proves this for its driver, identification with deployed source remains',
    'P','lead','Port1_Driver.rust identification; not an extra endpoint binder','Ledger_004/stdout.log')
for field,meaning in {
    'statement':'carried input statement equals input(s).statement',
    'stored':'carried stored bytes equal s.stored',
    'rows':'every carried proof row has the same erased message as input(s)',
}.items():
    add('D','Carried.'+field,BASE+'Port1_StoredCarrier.lean#Carried',
        meaning+'; SAME existential s; conditional domain guard inside annotated, already derived for lift/canon/enrich',
        'P','lead','Port1 lift_carried / canon_lift_carried / enrich_carried, reusable established predecessor','Ledger_004/stdout.log')

# Deployment obligations absent from both accepted-pair theorems. These are
# separate deliverables, not falsely presented as hidden theorem hypotheses.
future = [
 ('combine op34 and TX2 installation','lean/Op4P_Accepted.lean; lean/Tx2I_Accepted.lean','Produce ONE checked dictionary/witness chain with both installations, preserving all previous outputs','lead','S2 lead / Tx1Q_ / Tx2Q_'),
 ('shape full semantic/transcript join','lean/Op3I_Accepted.lean','Header acceptance is not semanticRows27, parseReached or transcript Aligned; connect full parser on SAME bytes','lead','S2 lead'),
 ('batch source Result/effects','lean/Op5I_AcceptedBatchCarrierCounterexample.lean','Install actual batch in TX1 AND TX2; full Result, effects, carrier, rejected-prefix semantics','lead','codex/cx-op5-tx2-20261025'),
 ('indexed authentication','docs/research/100bit-spend-path-20261013/lean/Port5Q1_Complete.lean','Q1 selected indexed openings authenticate to the committed root; root equality alone insufficient','lead','codex/cx-op5-tx2-20261025'),
 ('prepare Context/Data binding','docs/research/100bit-spend-path-20261013/lean/Port5Q1_QueryPorts.lean','Concrete source installation has the SAME model Prepared, transcript, scratch, rho/query context','lead','Tx1Q_ / Tx2Q_; SessionAPrepare retained'),
 ('TX1 ten-step query','docs/research/100bit-spend-path-20261013/lean/Port5Q1_Complete.lean','Bind actual query loop, geometry, reads, all64 weight rows, rhs and power on exact D189 cuts','lead','codex/cx-tx1-query-20261025'),
 ('TX1 flush materialization','docs/research/100bit-spend-path-20261013/lean/Port4C_FlushField.lean','Use actual returned pending state and Vec mutable-back function','lead','codex/cx-tx1-query-20261025'),
 ('TX1 writer/Q2 bridge','docs/research/100bit-spend-path-20261013/lean/Port5Q2_Checkpoint.lean','Prove dictionary bridge, line canonicality, caller/ROM, ObservationBinding, writer admission on SAME Vec','lead','codex/cx-tx1-query-20261025'),
 ('reader native/helper composition','docs/research/100bit-spend-path-20261013/lean/Port5Q2_ReaderValidate.lean','Compose bounded helper substitutions into actual op18, codec/iterator/allocator admission on retained bytes','lead','codex/cx-tx2-query-20261025'),
 ('powers same-return instance','docs/research/100bit-spend-path-20261013/lean/Port5Q1_Complete.lean','Identify resumed gamma and actual whole op17 power array, including no-read effects','session A','S1/S3 primitive ownership; Tx2Q_ integration'),
 ('initial/pending native instance','docs/research/100bit-spend-path-20261013/lean/Port3_Constructor.lean','Installed content constructor theorems need actual Copy/Std/allocator/runtime carrier interpretation','lead','S2 lead; Q1 installation integration'),
 ('finish full effects','lean/Tx2I_Finish.lean','FinT Boolean value equality on actual returned state does not yet transport Result/errors and ordered log','lead','FinT_ / Tx2Q_ / S2 interpreter'),
 ('S6 native decoded/public transport','docs/research/100bit-spend-path-20261013/lean/ClaimsUnrolledSdk.lean','Candidate semantic getters and public decoder need native Box/ownership/error/cleanup/adoption correspondence','session A','S6 owner; S2 same-call integration'),
 ('Claims native std slots','docs/research/100bit-spend-path-20261013/lean/ClaimsUnrolledFinish.lean','reserve/intoBox and explicit mapError/boxArray are value models; native ownership/abort/effects not proved','lead','S2 lead with S6/Claims owner'),
 ('remaining primitive instances','lean/Tx2I_Accepted.lean','Instantiate SessionAPrepare/Primitives/Basis/Backends, domain/geometry and nested S3/S4/S5/S9 laws at concrete actual operands','session A','Session A; no candidate modified'),
 ('library/native frame','docs/research/100bit-spend-path-20261013/lean/Port1_Library.lean','Content/library joins need actual native std/runtime/ABI/source dictionary association','lead','S2 lead'),
 ('history protection / Pool-ASQ8','docs/research/100bit-spend-path-20261013/lean/S2X_RuntimeRetention.lean','Construct the SAME protected key/version save/load history; distinguish Pool ASQ8, ASF8 public and1768 verifier CP','lead','S2 lead / RowOrder history; no assigned complete concrete instance'),
 ('oracle model order','docs/research/100bit-spend-path-20261013/lean/Port1_ModelOrder.lean','Compose per-body frozen2 interpreter with exact states, read order, duplicate handling, early exits and rejected oracle prefixes','lead','S2 lead; largest shared deployment composition gap'),
 ('raw canonical join','docs/research/100bit-spend-path-20261013/lean/Port1_CanonicalJoin.lean','Instantiate canonicalJoin.verifier from actual dictionary interpretation, rather than assuming its conclusion','lead','S2 lead'),
 ('two annotation passes','docs/research/100bit-spend-path-20261013/lean/Port1_CanonicalJoin.lean','Apply existing lifting on SAME raw/physical source instance; no new raw all-Input equality','lead','S2 lead / Port1'),
 ('canonical per-attempt endpoint','docs/research/100bit-spend-path-20261013/lean/Port1_CanonicalHeadline.lean','Compose canonical transport with Frozen2StartChargeProbability and per-attempt Claims: Port1 endpoint currently returns older OraclePortHeadlineFrozen2.Claims','lead','S2 lead; no checked canonical-per-attempt composition asserted'),
 ('deployed stored experiment','docs/research/100bit-spend-path-20261013/lean/OraclePortRuntimeBindingC7.lean','Instantiate full StoredCarrierBinding including runtime accepted run, physical bounds, whole carried data and oracle world','lead','S2 lead / external runtime admission'),
 ('source lowering to frozen ELFs','design/SOUND-INT-20261025.md','Pin native interpreter, source/compiler/features/wire/runtime to the three actual release ELFs; historical pins do not migrate themselves','lead','S10 / SBF owner and S2 lead'),
 ('coherent frozen replay','design/SOUND-INT-20261025.md','One final exact dependency closure replay after focused integration, with target/exit/wall/RSS/swap/revision','lead','Release lead; not run by audit'),
 ('final axioms/trust audit','AGENTS.md','Audit final composed dependency closure and explicit accepted trust list; current cached prints alone are not release audit','lead','Release lead; standard-only endpoint audits reused/newly printed'),
]
for name,definition,meaning,owner,job in future:
    add('E',name,definition,meaning,'P',owner,job,'../sound-int-20261025/manifest.json; design/SOUND-INT-20261025.md')
for name,definition,meaning in [
    ('P7 compiler/LLVM/toolchain','design/SOUND-INT-20261025.md','Accepted compiler/toolchain correctness trust; exact frozen source/artifact association remains proof/integration work'),
    ('P6 Kani association','evidence/op4-p6-20261025/P6-EQUIVALENCE.md','Accepted external Kani/P6 source-step association and its precise scope, not a new Lean axiom'),
    ('runtime allocator/entrypoint/syscall','docs/research/100bit-spend-path-20261013/lean/S2W_D189Wrappers.lean','Accepted Solana runtime, private allocator, abort/rollback and entrypoint semantics; no automatic concrete history instance'),
    ('TrustedStd.option_ok_or','docs/research/100bit-spend-path-20261013/lean/Port1_Library.lean#TrustedStd','∀ x,e, ops.op0 x e equals emitted okOr; exact Result/error semantics'),
    ('TrustedStd.result_unwrap32','docs/research/100bit-spend-path-20261013/lean/Port1_Library.lean#TrustedStd','∀ x, ops.unwrap32 x equals emitted unwrap32; failure/panic behavior retained'),
    ('cryptographic security contract','docs/research/100bit-spend-path-20261013/design/SECURITY-CONTRACT-20261021.md','Ideal-oracle/cryptographic model assumptions in fixed failure game and collision accounting; do not turn source gaps or P2Prime into cryptographic axioms'),
]:
    add('E',name,definition,meaning,'T','external','Accepted external trust retained; pin scope at release','Ledger_003/receipt.json; ../op4-p6-20261025/HANDOFF.md')
for field,meaning in {
    'oracle':'total digest equals ok(rawOracle H input) on every input; stronger than the success-only syscall law',
    'binary_parent':'∀ left,right, callback eval is exactly the singleton (parts(left,right),H(parts)) log and H(parts) result',
    'occupied_parent':'∀ left,right, occupied callback has exactly the singleton parent-query log and corresponding H result',
    'sibling_parent':'∀ left,right, sibling callback has exactly the singleton parent-query log and corresponding H result',
    'leaf':'∀ p,q,kind,pos,s with s.n<16, eval of actual leaf equals eval of referenceLeaf, including full Result/state/log',
}.items():
    add('E','P6Boundary.'+field,BASE+'MultiproofConeP6Frozen2Stage.lean#P6Boundary',
        meaning+'; mathematical callback instance, separate from external P6 tool/source association',
        'P','lead','codex/cx-op5-tx2-20261025; source/hash primitive reduction','Ledger_006/stdout.log')


def render():
    assert len({r['name'] for r in rows}) == len(rows)
    counts = {g: dict(Counter(r['classification'] for r in rows if r['group'] in g)) for g in ['ABC','D','E','ABCDE']}
    owners = {g: dict(Counter(r['owner'] for r in rows if r['group'] in g)) for g in ['ABC','D','E','ABCDE']}
    (OUT/'premises.json').write_text(json.dumps(dict(counts=counts, owners=owners, rows=rows),indent=2)+'\n')
    table = ['| Scope | T | P | C | lead | session A | external |','|---|---:|---:|---:|---:|---:|---:|']
    for g,label in [('ABC','Deduplicated accepted-pair input/continuation families'),('D','Headline/transport premise families'),('E','Additional deployment deliverables/trust items'),('ABCDE','All ledger rows (not independent proof gates)')]:
        table.append('| '+label+' | '+' | '.join(str(counts[g].get(k,0)) for k in ['T','P','C'])+' | '+' | '.join(str(owners[g].get(k,0)) for k in ['lead','session A','external'])+' |')
    text = '''# Soundness premise ledger — 25 October 2026

**Target not yet established. No premise is discharged by this audit.**

'''+ '\n'.join(table)+'''

**Highest-fan-out blocking premise: `firstMarks.source`** (class C, lead; Op5T_ Stage A). It quantifies over every TX1-marked returned event, including rejected child results, and requires the complete successful site layout without a success guard. Under a faithful deployed child trace this conflicts with the wrong-split rejected prefix in `Op5C_RejectedMarks`; the existing `ChildConeJoin.erasure` alone does not force faithful event lists. It gates the shared schedule used by both accepted-pair theorems and their Required14 continuations. This is a source-instance/vacuity obstruction, not a proof that the abstract theorem's arbitrary port type is empty. `secondMarks.source` needs the analogous audit. After that repair, the shared largest deployment gap is the concrete raw canonical source/frozen2 ordered-log join; no measured fan-out count is asserted.

## Reading and counting this ledger

Snapshot: branch `codex/cx-premise-ledger-20261025`, input revision in `input-pins.json`. This ledger supersedes premise counts based only on visible argument counts for these targets. It does not supersede any theorem, security contract or other worker's source. T = accepted external trust; P = implementation/model/instance proof obligation (also explicitly labelled event or budget conditions); C = contradictory or vacuity-suspect source instance. Ownership means accountable cone owner, not a claim that a job has completed the row. Jobs come from retained scratchpad prompts and `design/SOUND-INT-20261025.md`; they may run separately after this snapshot. No live sibling worktree was inspected or edited.

A row is one quantified atomic law family, not one scalar instance: `∀ k<3` and `∀ j:Fin22` stay quantified. Conjunction leaves are split; existential witnesses and all implication guards remain SHARED across their rows. Thus the two Matches leaves must use the SAME successor w′, the four PhysicalRange leaves the SAME start/end, and checkpoint history the SAME key/ledger/events. This is an inventory, not a claim that independently existential leaves are equivalent to the original statement. Payload equalities are not decomposed into byte-by-byte cells. Subtype/vector bounds are carrier well-formedness, not additional security assumptions. Repeated families across the two theorems appear once; distinct TX1/TX2 initial states, two rounds and two batches remain distinct. Data-only record fields are inventoried separately below. Some entry validity facts are definitionally satisfied by Entry.heap or implied by stronger admission fields; they remain listed to expose fields and are not independent open proof gates. Counts are therefore syntactic audit counts, not a security progress percentage.

The two accepted-pair theorems are **different specializations**, not a checked combined theorem:

- op34: `sdkOps adapterOps (Op3I_Install.install (Op4P_Install.install ops)) B claimsStd`.
- TX2: `sdkOps (Tx2I_Install.install adapterOps stageBase finishOps) (Op3I_Install.install ops) B claimsStd`.

`B`, `claimsStd`, the free operation fields, runtime and source association still need concrete instances. The op34 scan conclusion is absent from the TX2 theorem. Installing the union needs a checked same-witness composition; neither result implies that union by name alone.

## Mechanical statements and field expansion

Successful Lean transcripts: [accepted-pair signatures and fields](../evidence/premise-ledger-20261025/Ledger_003/stdout.log), [headline/Port1 signatures and fields](../evidence/premise-ledger-20261025/Ledger_004/stdout.log), [carrier/dictionary fields](../evidence/premise-ledger-20261025/Ledger_005/stdout.log). Helpers use `pp.all false`, `#check @...`, full names and `#print` definitions. Explicit named binder source blocks are retained in `Op4P_Accepted-explicit-binders.lean.txt` and `Tx2I_Accepted-explicit-binders.lean.txt`; together these avoid losing binder names when Lean prints an implication as an arrow. The first two failed diagnostic attempts also preserve maximally explicit notation, but receive no successful-audit credit. There are no new theorem declarations.

All original explicit binders, including the post-existential ones, must be read with the exact retained transcripts. A compact outline of their logical order is:

```
sdk, std, admission1, admission2, extraction, p1, syscall,
accepted1, accepted2, p:Params, port:ChildConeJoin, FirstMarks, SecondMarks
  → ∃ SAME f,s,outer,pre,middle,fs,ss,
      SourceCuts ∧ installed-header[/scan or TX2/finish] ∧ traces/frames/Claims
      ∧ ∀ decode,nodes,y1,
        writer → reader → history → P2Prime → entry → multiproof → scan
          → ∃ parsed, S2CallerFacts ∧ reached-site equivalence
```

TX2's additional finish output is itself universally conditional on `r0`, `r1`, all primitive return equations, `parsed,q,tr,i`, input/read/decode bindings, pairing/matching/semantic/dot/canonicality laws, `saved_ten` and `twelve`. These are group C below. They are not outer premises needed merely to obtain the existential TX2 calls; they ARE still needed to apply the advertised finish/model conclusion. Exported op18/op6/op9/finish successes and SourceCuts are conclusions, never newly counted as assumed cuts. Group B similarly lists premises needed to obtain the Required14 conclusion, not to obtain f,s.

No new top-level typeclass parameter occurs in either accepted-pair signature. Field/Fintype/DecidableEq/Algebra parameters shown in generic PairingLaws/EquationEndpoint definitions are instantiated by the existing concrete model field in this theorem, not unsupplied session A instances. `#print` exposes their generic parameters; actual source/backend correspondence is still group C. The `F` in `finishOps : FinishOps F` is its weights carrier, not a newly assumed Field F. FS2.Params does contain the three separately counted Prop fields, although its p binder is unused here. `root` and `length` also carry no authentication conclusion.

'''
    titles={'A':'Common outer antecedents, including hidden fields','B':'Shared post-existential Required14 continuation','C':'TX2 finish continuation, expanded to atomic laws','D':'Headline and Port1 transport premises','E':'Deployment obligations absent from both accepted-pair theorems'}
    for group,title in titles.items():
        text+='## '+title+'\n\n| ID / name | Defined at | Meaning | Class | Owner | Removing job / retained boundary | Evidence |\n|---|---|---|:---:|---|---|---|\n'
        for r in rows:
            if r['group']!=group: continue
            vals=[r['id']+' / `'+r['name']+'`','`'+r['definition']+'`',r['meaning'],r['classification'],r['owner'],r['job'],r['evidence']]
            text+='| '+' | '.join(v.replace('|','\\|').replace('\n',' ') for v in vals)+' |\n'
        text+='\n'
    text+='''## Data dictionaries are not discharged laws

The complete field inventories are in Ledger_003 and Ledger_005. They expose what a concrete deployment must identify without treating each arbitrary function value as a proof that it refines the model:

- Library: related, accountData, accountLamports, cellPayload, cellCounter, liveGuard, allocated, run. SDK semantics are exactly the fifteen adopted fields, expanded above; Matches additionally exposes its typed reply and related successor under one witness. Enabled/Fresh guards and Valid are printed. Enabling guards inside a universally guarded library law are not extra unconditional caller hypotheses.
- Allocator: allocate, cleanup. No account-heap effect law is smuggled in: this model gives those operations only their private A state. Admitting the real allocator to this separation is runtime trust plus concrete deployment association.
- Entry: handles, records, buffers, base, provenance. Record: owned account, lamports, rentEpoch. Heap: accounts, ownerLive, allocated, payload, counter, external, guards, ambient. Payload: descriptor/contents; Descriptor: base/length/provenance; Guard: token/cell/owner/kind/descriptor. These are data, with validity laws already expanded in A.
- ChildConeJoin: execute plus erasure. Free execute can manufacture site annotations unless identified with the faithful installed source trace; erasure alone binds only its result. FirstMarks cannot receive source-faithfulness credit from this record.
- B/FinishModel.Boundaries: fromFn, mask, add, mul, terminal, circle, unwrapRoot, claims. ClaimsUnrolledFinish installs its Claims value interpretation; arbitrary B fields are not certified primitive implementations. StdCalls: reserve, intoBox. Native std/ownership/effects obligations are group E.
- `adapterOps : AdapterRw.Ops`, `ops : AspisR1CurrentCaller.Ops`, `stageBase : VTop_Stages.Ops`, `finishOps : AspisR1Stage2.Stage2Finish.FinishOps F`: every field's exact type is printed in Ledger_005. Slot numbering depends on dictionary: current-caller op6 is batch, op7 query, op16 writer, op17 flush, op18 pending, op19 geometry; stage op5 is batch, op6 query, op8 writer, op9 flush, op18 reader, op19 finish. Current-caller op5 is wide_view. `sdkOps`, op3/op4 and TX2 install override selected slots; the remaining source/body installations are group E. No free slot is certified by having a concrete-sounding name.
- Params: D/hL/enc/encLen/dec/decEnc/lbl/σ/iv/rounds. Only hL, encLen and decEnc are Prop fields. RoundValues: six value fields c0,c4,lhs,quarter,rhs,value and six Prop fields per round (group C). CheckpointVersionBinding: key/ledger/events are data witnesses; its three laws are group B. Parsed/q/tr/i, HeaderDecode, nodes and y1 remain explicit quantified carriers; hi/hq/read/decoded bind them only in the conditional finish result.
- Canonical Submission has publicBytes and stored, both arbitrary Bytes. Carried has one SAME Submission witness with exact statement equality, stored equality and erased message equality for every row. Physical is the equality law in D. Decoder is a function to an optional sampler, not a structure containing a hidden source-refinement proof. AcceptedRunJoin has exactly verifier and annotated in each variant, expanded in D. StoredCarrierBinding is the whole accepted-run equality printed in Ledger_004.

Carried's three equalities are a domain condition in `canonicalJoin.annotated`, not extra unconditional endpoint assumptions: input/lift/canon/enrich preservation is already proved in Port1. The original endpoint quantifies arbitrary logical Input; the canonical endpoint changes that carrier explicitly. It returns `OraclePortHeadlineFrozen2.Claims`, **not** the newer PerAttempt Claims. The missing corrected canonical per-attempt composition must remain visible. Neither Boolean finish equality nor two annotation passes by themselves identify the deployed experiment.

## Conclusions and release boundary

The requested endpoint's Claims is a conjunction of: accepted extractor mean cost at attempt budget(Q+1161); every returned witness satisfies LiteralProtocol.relation; abort allowance 2^-126+2^-454≤2^-120; failureModel≤totalBound(Q); and, if Q≤Qmax, failureModel≤(Q+1)·2^-100. These are printed CONCLUSIONS, not additional premises. The security contract also requires the explicit repeated/adaptive bound with (Q+34)·B, collision κ(Q+1161), extractor abort and scan exhaustion, including the zero-query corollary; it forbids grinding/work-normalization credit. No deployment or100-bit conclusion is claimed here.

P2Prime is deliberately P. Matching SHA digests do not logically imply byte equality. A protected-history argument or the existing bounded collision-event accounting must justify the concrete source instance; no unconditional injectivity assumption is accepted. Similarly, noInterveningWrite is P even though runtime rollback semantics are T. The authority/permissions/history that protect a specific checkpoint version require proof. Child slot joins, SessionA primitives and source-to-model correspondence are P, never added to the external crypto trust list.

## Validation, freeze and handoff

Five Lean invocations used out of15; zero Kani out of0. Ledger_001 and002 exit1 solely for unsupported `pp.width`; sources/logs retained and excluded. Changed helpers use `format.width`; Ledger_003/004/005 exit0. No timeout, memory kill, unchanged retry, raised cap, dependency rebuild, package replay, Rust or ELF build. All jobs use unchanged S2W launchers in the task-private host directory, -j1 -M7000, individual MemoryHigh=6G / MemoryMax=8G / MemorySwapMax=0 / TasksMax=64 scopes. The admission inspection saw one existing other-worker scope; this task added at most two8GiB scopes, under55GiB. No shared object was overwritten. This is a cached signature audit across two deliberately separate dependency selections, not a coherent combined release replay.

Receipts for every invocation record exact target/command, source hash, source revision anchor, selected dependency/sidecar fingerprint, exit, wall, peak RSS, swap and full axioms lines. `validation-summary.json` records the final helper hashes and reused evidence pins. New successful endpoint prints are exactly [propext, Classical.choice, Quot.sound]; no new theorem or axiom was declared. Revision a8f85a1c67 plus dirty helper hashes identifies the checked inputs. Source revisions and timings from historical proofs are retained in their original receipts, never reassigned to this audit. The field inventory helper has no theorem and therefore no new theorem axioms result (empty print list).

No assumptions discharged, added, or changed. No existing statement, quantifier, carrier, failure event or metric changed. The ledger identifies source-instance and vacuity risks without repairing them. No shipped/cfg(kani) file, session A candidate, other live worktree, key, protocol parameter, feature or wire format changed. ELF rebuild trigger did not fire. Inherited, NOT freshly reproduced: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4; devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299; Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548. No binaries/objects/ELFs/archives committed. No push.

Next deliverable: Op5T_'s success-conditioned faithful marks instance and joint non-vacuity, then same-run concrete batch/query/writer/reader installations and the raw canonical ordered-log join. Recount only after comparing the full before/after statements and expanding every new record field. Removing a binder by moving its law into a record or post-existential implication earns no premise-removal credit.
'''
    text = text.replace('Five Lean invocations used out of15', 'Seven Lean invocations used out of 15')
    text = text.replace('zero Kani out of0', 'zero Kani out of 0')
    text = text.replace('Ledger_003/004/005 exit0', 'Ledger_003/004/005/006/007 exit0')
    text = text.replace('in Ledger_003 and Ledger_005.', 'in Ledger_003 and Ledger_005; Ledger_006 expands P6Boundary callback laws and the Port1 library trust fields.')
    text = text.replace('Carried\'s three equalities are a domain condition', 'Carried\'s three equalities, listed separately in D, are a domain condition')
    resources = '\n| Attempt / exact target | Exit | Wall seconds | Peak RSS KiB | Swap | Axioms print |\n|---|---:|---:|---:|---:|---|\n'
    for i in range(1,8):
        r = json.loads((OUT/f'Ledger_{i:03}'/'receipt.json').read_text())
        status = 'standard three' if r['print_axioms'] else 'N/A: fields only, no new theorem'
        if i < 3:
            status += '; failed option diagnostic, excluded'
        resources += f'| Ledger_{i:03} / {r["sources"][0]} | {r["exit_status"]} | {r["wall_seconds"]:.6f} | {r["peak_rss_kib"]} | {r["swaps"]} | {status} |\n'
    resources += '\nAll seven use source revision anchor `a8f85a1c670e4a3646a5567f460298ebec45612d` plus the exact dirty helper source hashes in their receipts. Successful source hashes match the committed helpers. Original theorem source hashes match their retained successful receipts; the imported PerAttempt object hash also matches its original receipt. This does not certify a full transitive release rebuild.\n\n'
    text = text.replace('Only hL, encLen and decEnc are Prop fields.', 'Only hL, encLen and decEnc are Prop fields. Ledger_007 additionally exposes SourceInputs, MatchingSupport.Data/Functional, LinearMap/AddHom, Parsed, erased Prefix, UnifiedSampler.Public, R0P.Public and the generic Field class. The model Functional linearity fields and named public initFits proof are listed in C; they are supplied structurally by their model types. SourceInputs itself has only decoded/data/m31/queryBytes/state31/m32/rho/state32; Data has W/V/F/F0/Y/c0/gamma/kappa/alpha0/alpha1/p0/p1/f. Parsed contains wire/semantic; Prefix contains statement/rounds. No source arithmetic instance follows from these model carriers.')
    text = text.replace('No assumptions discharged, added, or changed.', resources+'No assumptions discharged, added, or changed.')
    (ROOT/'design/PREMISE-LEDGER-20261025.md').write_text(text)


if __name__ == '__main__':
    render()
