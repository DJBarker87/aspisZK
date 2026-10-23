#!/usr/bin/env python3
"""Read-only packet checks and reproducible manifest generation; no prover replay."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
R=Path(__file__).resolve().parents[2]; E=R/'evidence/s2w-20261023';L=R/'docs/research/100bit-spend-path-20261013/lean'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inv=json.loads((E/'source-inventory.json').read_text())
for p,v in inv['sources'].items():assert sha(R/p)==v['sha256'],p
native=(R/'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs').read_text()
fragment=native[native.index('struct OwnedAccount {'):native.index('\nfn require_readonly_buffer')]
harness=(R/'tools/s2w-20261023/S2W_native/src/lib.rs').read_text()
assert harness.startswith('#![cfg(kani)]') and harness.count(fragment)==1
assert native.count('accounts[2].try_borrow_mut_data()?.copy_from_slice(&checkpoint);')==1
assert harness.count('accounts[2].try_borrow_mut_data()?.copy_from_slice(&checkpoint);')==1
assert sha(L/'S2W_Snapshot.lean')==json.loads((E/'snapshot-emission/adaptation.json').read_text())['adapted_sha256']
allowed={'propext','Classical.choice','Quot.sound'}
current={'S2W_OracleAudit':'lean-001','S2W_Snapshot':'lean-003','S2W_SnapshotFacts':'lean-010','S2W_SnapshotJoin':'lean-012','S2W_Audit':'lean-013','S2W_Trace':'lean-016','S2W_Outer':'lean-021','S2W_OuterErasure':'lean-032','S2W_TraceFacts':'lean-026','S2W_Observation':'lean-033','S2W_ChildTrace':'lean-035','S2W_ContinuationAudit':'lean-037','S2W_TrustedStd':'lean-038','S2W_ChildJoins':'lean-040','S2W_ClosureAudit':'lean-042','S2W_LeadInterface':'lean-045','S2W_SuccessOracle':'lean-046','S2W_WrapperLaws':'lean-050','S2W_EntryWriteHistory':'lean-052','S2W_FinalAudit':'lean-053','S2W_ExtractionBoundary':'lean-055','S2W_AuthenticatedInputs':'lean-056','S2W_NativeConsolidation':'lean-058','S2W_SiteSchedule':'lean-061','S2W_InputSchedule':'lean-062','S2W_ChildEventPorts':'lean-064','S2W_TwoFieldAudit':'lean-066','S2W_DigestExtraction':'lean-068','S2W_D188Consolidation':'lean-069'}
for module,a in current.items():
 p=E/a/'receipt.json';v=json.loads(p.read_text());assert v['exit_status']==0
 assert v['source_hashes'][module+'.lean']==sha(L/(module+'.lean'))
 assert v['print_axioms']
 for line in v['print_axioms']:
  match=re.search(r'depends on axioms: \[([^]]*)\]',line,re.S)
  if match:assert set(s.strip() for s in match[1].split(','))<=allowed,(module,line)
for p in L.glob('S2W_*.lean'):
 assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats|allowUnsafeReducibility)',p.read_text()),p
expected={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
receipts=[]
for p in sorted(E.glob('*/receipt.json')):
 x=json.loads(p.read_text());assert x['limits']==expected,p
 assert x['swaps']=='0',p
 for f,digest in x['source_hashes'].items():assert sha(p.parent/'sources'/f)==digest,(p,f)
 assert (E/(x['attempt']+'-reservation.json')).exists(),p
 receipts.append({k:x.get(k) for k in ['attempt','kind','source_revision','source_hashes','deps_fingerprint','command','exit_status','wall_seconds','peak_rss_kib','swaps','cgroup_memory_peak_bytes','print_axioms']})
lean_compiles=sum(x['kind']=='lean' for x in receipts)
preflights=[p.stem for p in sorted((R/'tools/s2w-20261023').glob('lean-*.json')) if not (E/p.stem/'receipt.json').exists()]
assert preflights==['lean-039','lean-060'],preflights
assert 'FileNotFoundError: S2W_SiteSchedule' in (E/'lean-060-launcher.log').read_text()
assert 'FileNotFoundError: S2Y_ForestPublic' in (E/'lean-039-launcher.log').read_text()
lean=lean_compiles+len(preflights);kani=sum(x['kind'].startswith('kani') for x in receipts)
assert lean<=100 and kani<=60
fields={
 'proofBytes':'Proved on fixed-invocation constructed projection by authenticated_inputs and input_schedule; actual child event exporters are named per-child joins',
 'publicBytes':'Proved on constructed projection from complete-buffer P2Prime and the writer/reader header child joins; FullForestAcceptedRoundtrip is not required by this authentication route, not proved',
 'proofSuffix':'Both native owned source cuts derived; constructed projection field proved with authenticated sameStoredProof',
 'proofLength':'Actual native owned TX1 field derived under AeneasExtraction; 57607',
 'checkpointBytes':'Constructed save/tx2/resume projection proved under existing CheckpointVersionBinding indexed to returned vector; source write-to-committed-version association is still required for actual native instance',
 'checkpointLength':'Derived from named checkpoint serialization child size theorem on actual accepted child output; no OwnedSnapshotShape or entrySize premise',
 'nodeViews':'Proved on constructed projection under separate parser/multiproof child joins; sameStoredProof derived via header checks and P2Prime',
 'y1Input':'Proved on constructed projection under exact named S8 range child join; tx1ProofObservation is definitional',
 'observerNone':'Constructed retained-input observation uses actual extracted None at both fixed calls; no universal ChildInputRetention',
 'reachedPrefix':'Proved for source-mark schedule projection under fixed-invocation child event ports. Native outer-log to expanded child timeline splice at op10/op11 still needs source composition',
 'callOrder':'Proved for source-mark schedule at actual prefix positions, not Site.rank. Actual parent pre/middle trace selection and outer-to-child splice remain unproved',
 'accountFrame':'NOT discharged: actual before/after account observations remain arbitrary. Need compose interpreted wrapper frame with actual native wrapper observation; child-local frames belong to child joins',
 'writtenMetadata':'NOT discharged: same native wrapper/account observation composition. Existing projected Kani metadata checks and interpreted copy frame are not yet this global source instance',
 'oracle':'Success-conditioned field under named source-level AeneasExtraction, RuntimeSyscall and P1. NativeBinding is derived from the exact reused extracted digest/hash-to-bytes body, not assumed as an opaque-op43 interpretation. No totality; multiproof P6 totality stays child-owned'}
manifest={'schema':'focused-extractor-proof-packet-v1','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'qualification':'D188 extraction boundary, one accepted native owned trace and derived cuts, checkpoint authentication and twelve-field fixed-invocation input/schedule projection. Separate child event/source hypotheses permitted by D188. Full S2CallerFacts NOT established: actual native wrapper/frame and committed-version observation composition remains. No native/extraction association assigned to S2. Focused cached validation only, not coherent release replay. Failed recovery axioms excluded; kani005 GNU-time peak is parent-only.','budget':{'lean_used':lean,'lean_compile_invocations':lean_compiles,'lean_preflight_failures':preflights,'lean_limit':100,'kani_used':kani,'kani_limit':60},'new_trust':['AeneasExtraction (D188 named existing project extraction boundary)','S2W_TrustedStd.TrustedStd.slice_copy_from_slice (inherited continuation2; unchanged)'],'child_join_structures':['FirstEntryVerifierConeJoin','MultiproofConeJoin','S8StageConeJoin','S7StageConeJoin','CheckpointConeJoin','FullForestConeJoin','CheckpointWriterConeJoin','CheckpointReaderConeJoin','FirstEntryEventConeJoin','SecondEntryEventConeJoin'],'current_lean':current,'fields':fields,'receipts':receipts,'production_source_pins':inv['sources'],'release_pins_reused':inv['release_pins']}
text=json.dumps(manifest,indent=2)+'\n'
if '--check' in sys.argv:
 old=json.loads((E/'manifest.json').read_text());assert {k:v for k,v in old.items() if k!='source_revision'}=={k:v for k,v in manifest.items() if k!='source_revision'}
else:(E/'manifest.json').write_text(text)
print(json.dumps({'status':'pass','lean':lean,'kani':kani,'current_modules':len(current),'fields':len(fields)}))
