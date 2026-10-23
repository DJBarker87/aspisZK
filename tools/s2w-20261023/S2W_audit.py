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
current={'S2W_OracleAudit':'lean-001','S2W_Snapshot':'lean-003','S2W_SnapshotFacts':'lean-010','S2W_SnapshotJoin':'lean-012','S2W_Audit':'lean-013'}
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
lean=sum(x['kind']=='lean' for x in receipts);kani=sum(x['kind'].startswith('kani') for x in receipts)
assert lean<=100 and kani<=60
fields={
 'proofBytes':'Conditional inherited; same native invocation/site observations and authenticated TX2 proof identity open',
 'publicBytes':'Conditional inherited; FullForestAcceptedRoundtrip, reconstruction identity/source installation and native site retention open',
 'proofSuffix':'Conditional inherited; outer accepted source cuts proved; native observed1/2 and written/current digest binding open',
 'proofLength':'Discharged by inherited AdapterRw accepted TX1 proof shapes (actual native association still enclosing obligation)',
 'checkpointBytes':'Conditional inherited; CheckpointVersionBinding plus save/tx2/resume native cuts open',
 'checkpointLength':'Improved local source join: snapshot return + accepted owned TX1 derive1768 without OwnedSnapshotShape/entrySize; native association/savedAtWrite open',
 'nodeViews':'Conditional inherited; NodeRanges, sameStoredProof and actual parser/physical internal sites open',
 'y1Input':'Conditional inherited; firstChildY1Range, tx1ProofObservation and actual parser/internal site open',
 'observerNone':'Conditional inherited; extracted observer=None; propagation into actual internal reached sites open',
 'reachedPrefix':'Open; no native ordered child/site observation constructed',
 'callOrder':'Open; no native clocks/order constructed',
 'accountFrame':'Open globally; native checkpoint-write destination leaf passed; other allocations/children/composition open',
 'writtenMetadata':'Open globally; per-operation destination metadata/lamports preservation passed; native site join open',
 'oracle':'Conditional; NativeBinding open, RuntimeSyscall successful-return law insufficient for exact unrestricted field; independently proved total-return/source theorem needed'}
manifest={'schema':'focused-extractor-proof-packet-v1','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'qualification':'Focused cached new modules and standalone native leaf gates. No S2CallerFacts/native-observation theorem or coherent release replay. Failed recovery axioms excluded. GNU time peak for timeout kani005 is parent-only; cgroup peak retained.','budget':{'lean_used':lean,'lean_limit':100,'kani_used':kani,'kani_limit':60},'current_lean':current,'fields':fields,'receipts':receipts,'production_source_pins':inv['sources'],'release_pins_reused':inv['release_pins']}
text=json.dumps(manifest,indent=2)+'\n'
if '--check' in sys.argv:
 old=json.loads((E/'manifest.json').read_text());assert {k:v for k,v in old.items() if k!='source_revision'}=={k:v for k,v in manifest.items() if k!='source_revision'}
else:(E/'manifest.json').write_text(text)
print(json.dumps({'status':'pass','lean':lean,'kani':kani,'current_modules':len(current),'fields':len(fields)}))
