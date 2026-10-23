from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];D=R/'docs/research/100bit-spend-path-20261013';E=D/'evidence/s2e-20261023'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[];snapshot_mismatches=[]
for p in sorted(E.glob('*/receipt.json')):
 x=json.loads(p.read_text());assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},p
 assert x['swaps']=='0',p
 for f,h in x['source_hashes'].items():
  snapshot=p.parent/'sources'/f
  if not snapshot.exists():
   assert f.endswith('.llbc'),(p,f)
  elif sha(snapshot)!=h:snapshot_mismatches.append({'receipt':str(p.relative_to(R)),'source':f,'recorded':h,'snapshot':sha(snapshot)})
 if x['kind']=='lean' and x['exit_status']==0:
  assert x['print_axioms'],p
  for line in x['print_axioms']:
   assert 'sorryAx' not in line,p
   if 'depends on axioms:' in line:assert set(re.findall(r'\[([^]]*)\]',line)[0].split(', '))<={'propext','Classical.choice','Quot.sound'},(p,line)
 if x['kind']=='kani' and x['exit_status']==0:
  text=(p.parent/'stdout.log').read_text();assert 'VERIFICATION:- SUCCESSFUL' in text,p
  matches=re.findall(r'\*\* (\d+) of (\d+) failed',text);assert matches and all(a=='0' for a,b in matches),p
 rows.append({'attempt':x['attempt'],'kind':x['kind'],'target':x['command'],'exit_status':x['exit_status'],'wall_seconds':x['wall_seconds'],'peak_rss_kib':x['peak_rss_kib'],'swap':x['swaps'],'source_revision':x['source_revision'],'source_hashes':x['source_hashes'],'print_axioms':x['print_axioms'],'receipt':str(p.relative_to(D)),'status':'focused accepted within stated model/domain' if x['exit_status']==0 else 'excluded failure/setup/timeout; no proof credit'})
assert not snapshot_mismatches,snapshot_mismatches
assert sum(x['kind']=='lean' for x in rows)<=100
assert sum(x['kind']=='kani' for x in rows)<=60
final=json.loads((E/'lean-023/receipt.json').read_text());assert final['exit_status']==0
for p in sorted((D/'lean').glob('S2E_*.lean')):
 assert final['source_hashes'][p.name]==sha(p),p
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s|set_option\s+(maxRecDepth|maxHeartbeats)',p.read_text(),re.M),p
source=(E/'S2E-reference/src/S2E_Reference.rs').read_text();assert '#![cfg(any(kani, aeneas_ref))]' in source
assert not re.search(r'\b(while|RefCell)\b|\.iter\(',source), 'reference extraction shape'
prior=D/'evidence/s2a-20261023/S2A-spec/S2A_Primitives.rs';assert sha(prior)==sha(E/'S2E-steps/src/S2E_Trusted.rs')
base=json.loads((E/'stage0.json').read_text())['source_revision']
shipped=subprocess.check_output(['git','diff',base,'--','crates','programs','Cargo.lock','Cargo.toml','.cargo'],cwd=R,text=True);assert not shipped
for mode in ['default','devnet','pool']:
 x=json.loads((E/f'S2E-sbf-{mode}-pin.json').read_text());assert x['byte_identical'] and x['sha256']==x['expected_sha256']
for p in E.rglob('*'):
 if p.is_file():assert p.suffix not in ['.olean','.so','.elf','.tar','.gz'],p
manifest={'schema':'focused-extractor-proof-packet-v1','status':'PARTIAL; native execution certificate and S2CallerFacts NOT established','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'budget':{'lean':sum(x['kind']=='lean' for x in rows),'lean_limit':100,'kani':sum(x['kind']=='kani' for x in rows),'kani_limit':60},'final_export_audit':'lean-023/receipt.json','final_dependency_pins':{'path':'S2E-host-pins.json','sha256':sha(E/'S2E-host-pins.json')},'source_snapshot_audit':'all present source snapshots match their recorded hashes; LLBC retained on host by hash/size only','new_native_Required14_fields_discharged':[],'shipped_changes':False,'artifacts':'S2E-sbf-{default,devnet,pool}-pin.json: all reproduced, SHA256 and size only','trust':'S2TrustedSdkBorrow unchanged; bounded checked SDK spec reused. Generic Ops/Children NOT instantiated proved contracts. No added axiom/trust.','release_limitations':'No coherent full frozen proof dependency replay or native/source/ELF/P6/runtime/ABI/oracle transport. Earlier attempts have incomplete immutable dependency fingerprints; final selected overlay pinned/verified.','attempts':rows}
(E/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'budget':manifest['budget'],'attempts':len(rows),'status':manifest['status'],'source_snapshots':'matched','shipped_changes':False}))
