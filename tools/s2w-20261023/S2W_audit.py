#!/usr/bin/env python3
"""Read-only packet checks and reproducible manifest generation; no prover replay."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
R=Path(__file__).resolve().parents[2]; E=R/'evidence/s2w-20261023';L=R/'docs/research/100bit-spend-path-20261013/lean'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inv=json.loads((E/'source-inventory.json').read_text())
delta=json.loads((E/'d189-inherited-source-delta.json').read_text())
assert delta['historical_sha256']==inv['sources'][delta['source']]['sha256']
for p,v in inv['sources'].items():
 expected=delta['current_sha256'] if p==delta['source'] else v['sha256']
 assert sha(R/p)==expected,p
native=(R/'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs').read_text()
fragment=native[native.index('struct OwnedAccount {'):native.index('\nfn require_readonly_buffer')]
harness=(R/'tools/s2w-20261023/S2W_native/src/lib.rs').read_text()
assert harness.startswith('#![cfg(kani)]') and harness.count(fragment)==1
assert native.count('accounts[2].try_borrow_mut_data()?.copy_from_slice(&checkpoint);')==1
assert harness.count('accounts[2].try_borrow_mut_data()?.copy_from_slice(&checkpoint);')==1
assert sha(L/'S2W_Snapshot.lean')==json.loads((E/'snapshot-emission/adaptation.json').read_text())['adapted_sha256']
allowed={'propext','Classical.choice','Quot.sound'}
current={'S2W_OracleAudit':'lean-001','S2W_Snapshot':'lean-003','S2W_SnapshotFacts':'lean-010','S2W_SnapshotJoin':'lean-012','S2W_Audit':'lean-013','S2W_Trace':'lean-016','S2W_Outer':'lean-021','S2W_OuterErasure':'lean-032','S2W_TraceFacts':'lean-026','S2W_Observation':'lean-033','S2W_ChildTrace':'lean-035','S2W_ContinuationAudit':'lean-037','S2W_TrustedStd':'lean-038','S2W_ChildJoins':'lean-040','S2W_ClosureAudit':'lean-042','S2W_LeadInterface':'lean-045','S2W_SuccessOracle':'lean-046','S2W_WrapperLaws':'lean-050','S2W_EntryWriteHistory':'lean-052','S2W_FinalAudit':'lean-053','S2W_ExtractionBoundary':'lean-055','S2W_AuthenticatedInputs':'lean-056','S2W_NativeConsolidation':'lean-058','S2W_SiteSchedule':'lean-061','S2W_InputSchedule':'lean-062','S2W_ChildEventPorts':'lean-064','S2W_TwoFieldAudit':'lean-066','S2W_DigestExtraction':'lean-068','S2W_D188Consolidation':'lean-069','S2W_CommittedCheckpoint':'lean-072','S2W_AccountObservations':'lean-074','S2W_ExpandedTrace':'lean-076','S2W_ExpandedChildren':'lean-080','S2W_OuterOccurrences':'lean-086','S2W_FirstOccurrence':'lean-087','S2W_TraceSplice':'lean-090','S2W_NativeSchedule':'lean-091','S2W_ReturnedCheckpoint':'lean-092','S2W_ScheduledConsolidation':'lean-093','S2W_D189Interpretation':'lean-095','S2W_EntryPrivileges':'lean-099','S2W_D189Entry':'lean-103','S2W_D189Wrappers':'lean-106','S2W_D189Consolidation':'lean-109','S2W_D189Audit':'lean-110'}
for module,a in current.items():
 p=E/a/'receipt.json';v=json.loads(p.read_text());assert v['exit_status']==0
 assert v['source_hashes'][module+'.lean']==sha(L/(module+'.lean'))
 assert v['print_axioms']
 for line in v['print_axioms']:
  match=re.search(r'depends on axioms: \[([^]]*)\]',line,re.S)
  if match:assert set(s.strip() for s in match[1].split(','))<=allowed,(module,line)
for p in L.glob('S2W_*.lean'):
 code=re.sub(r'/\-[\s\S]*?\-/|--[^\n]*','',p.read_text())
 assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats|allowUnsafeReducibility)',code),p
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
assert preflights==['lean-039','lean-060','lean-098','lean-101'],preflights
assert 'FileNotFoundError: S2W_EntryPrivileges' in (E/'lean-098-launcher.log').read_text()
assert 'FileNotFoundError: S2W_D189Entry' in (E/'lean-101-launcher.log').read_text()
assert 'FileNotFoundError: S2W_SiteSchedule' in (E/'lean-060-launcher.log').read_text()
assert 'FileNotFoundError: S2Y_ForestPublic' in (E/'lean-039-launcher.log').read_text()
lean=lean_compiles+len(preflights);kani=sum(x['kind'].startswith('kani') for x in receipts)
assert lean-69<=100 and kani-19<=40
fields={
 'proofBytes':'Proved on the ONE native wrapper observation by original native SDK payload interpretation, immutable owned snapshots, writer/reader header checks and complete-buffer P2Prime',
 'publicBytes':'Proved by authenticated full-buffer P2Prime route; FullForestAcceptedRoundtrip is not required or proved',
 'proofSuffix':'Proved from BOTH actual owned source suffix cuts and authenticated sameStoredProof',
 'proofLength':'Proved from actual owned TX1 acceptance: 57607',
 'checkpointBytes':'Proved from SAME returned vector through actual successful wrapper std copy/drop, actual post-write account version and TX2/resume loaded bytes; no savedAtWrite or returned-vector history substitution premise',
 'checkpointLength':'Proved:1768; snapshot deferred-length inversion and named writer child size; no OwnedSnapshotShape/entrySize premise',
 'nodeViews':'Proved under named first-entry parser/multiproof child-local source-range theorems, instantiated on the SAME authenticated actual source arguments',
 'y1Input':'Proved under the named S8 child-local checked7031/464 range; no tx1ProofObservation premise',
 'observerNone':'Proved from actual fixed extracted child calls and retained snapshots; no universal ChildInputRetention',
 'reachedPrefix':'Proved on actual expanded owned source log, with named child-local erasure/site marks; site membership explicitly identified with projected actual log',
 'callOrder':'Proved on SAME actual expanded source log; op10/op11 occurrences and pre/middle/post splice derived from source; clocks count projected event prefixes',
 'accountFrame':'Proved on full native wrapper Account observation under D189 interpretation: returned primitive copy/drop heap, source privilege-based alias exclusion, owned signature and private allocator account projections. No caller frame premise',
 'writtenMetadata':'Proved on SAME actual returned native wrapper heap, including full lamports/rentEpoch; no post-account or metadata equality premise',
 'oracle':'Proved revised success-conditioned field under exact digest extraction, RuntimeSyscall and P1; no totality, multiproof P6 totality stays child-owned'}

manifest={'schema':'focused-extractor-proof-packet-v1','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'qualification':'Continuation6/D189: FULL conditional S2CallerFacts proved for every accepted interpreted native wrapper pair. Initial SDK native-to-heap relation and primitive wrapper contracts instantiate the existing approved trust items; source wrapper inversion derives actual post-write heap, protected version and full metadata/account frames. Owned effect frame proved on SAME actual expanded source log. Runtime/library/extraction and named child premises remain explicit; none assumes a whole-caller conclusion. Focused cached dependency-union validation, not a full global release rebuild or proof of retained premises. Failed recovery axioms excluded; kani005 GNU-time peak is parent-only.','budget':{'lean_used':lean,'lean_compile_invocations':lean_compiles,'lean_preflight_failures':preflights,'lean_limit':169,'kani_used':kani,'kani_limit':59},'new_trust':[],'existing_trust_used':['AeneasExtraction (D188)','S2TrustedSdkBorrow (D189 native-to-heap interpretation)','TrustedStd slice copy, to_vec and cleanup semantics','Runtime allocator private-region/abort interpretation (P2-P4/RuntimeSyscall)','RuntimeEntrypointAdmission initial relatedness and metadata/cell interpretation'],'child_join_structures':['FirstEntryVerifierConeJoin','MultiproofConeJoin','S8StageConeJoin','S7StageConeJoin','CheckpointConeJoin','FullForestConeJoin','CheckpointWriterConeJoin','CheckpointReaderConeJoin','FirstEntryEventConeJoin','SecondEntryEventConeJoin','S2W_ExpandedChildren.ChildConeJoin','S2W_TraceSplice.FirstMarks','S2W_TraceSplice.SecondMarks'],'continuations_5_6_budget':{'lean_used':lean-69,'lean_limit':100,'kani_used':kani-19,'kani_limit':40},'current_lean':current,'fields':fields,'receipts':receipts,'production_source_pins':inv['sources'],'inherited_external_source_delta':delta,'release_pins_reused':inv['release_pins']}
text=json.dumps(manifest,indent=2)+'\n'
if '--check' in sys.argv:
 old=json.loads((E/'manifest.json').read_text());assert {k:v for k,v in old.items() if k!='source_revision'}=={k:v for k,v in manifest.items() if k!='source_revision'}
else:(E/'manifest.json').write_text(text)
print(json.dumps({'status':'pass','lean':lean,'kani':kani,'current_modules':len(current),'fields':len(fields)}))
