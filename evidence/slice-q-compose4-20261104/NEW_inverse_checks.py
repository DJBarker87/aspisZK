"""Strict direct-extraction/fidelity audit; no logged-clone shortcut."""
from pathlib import Path
import sys,json,hashlib,lzma,subprocess,re
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent
sys.path.insert(0,str(E.parent/'slice-q-compose3-20261102'))
from NET_inverse_checks import tok,functions
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
obj=lambda p:json.loads(Path(p).read_text())
LIMITS={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
FROZEN='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def receipt(a,want):
 r=obj(E/a/'receipt.json');assert r['exit_status']==want
 assert r['limits']==LIMITS and int(r['swaps'])==0 and int(r['peak_rss_kib'])>0 and r['wall_seconds']>0
 ad=obj(E/(a+'-admission.json'));assert ad['exit_status']==0 and ad['reservation']['allowed'] is True
 return r

def audit():
 ex=receipt('NEW_E003',0);pins=obj(E/'NEW_ACTUAL_EXTRACTION_PINS.json')
 assert pins['charon_exit']==pins['exit']==0 and pins['root_presence_checked'] is True
 assert pins['lock_before']==pins['lock_after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
 assert pins['charon_sha256']=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
 assert pins['aeneas_sha256']=='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'
 for path,h in pins['outputs'].items():assert sha(E/path)==h
 code=(E/'NEW_actual_extracted/NEW_InverseActual/Funs.lean').read_text()
 assert re.search(r'def aspis_core\.field\.M31\.inv\s',code) and re.search(r'def NEW_inverse\s',code)
 assert 'FunsExternal' not in code and not re.search(r'\b(?:axiom|sorry|admit|native_decide)\b',code)
 assert 'def aspis_core.field.square_n_loop.body' in code and 'def aspis_core.field.square_n_loop\n' in code
 frozen=subprocess.check_output(['git','show',FROZEN+':crates/aspis-core/src/field.rs'],cwd=R)
 assert pins['field_sha256']==hashlib.sha256(frozen).hexdigest()
 source=json.loads(lzma.decompress((E/'NEW_E003_OUTPUTS.json.xz').read_bytes()))
 for path in ['NEW_src/crates/aspis-core/src/field.rs','NEW_src/Cargo.lock']:
  assert hashlib.sha256(source['NEW_E003/sources/'+path].encode()).hexdigest()==ex['source_hashes'][path]
 assert source['NEW_inverse_extract/src/lib.rs']=='use aspis_core::field::M31;\npub fn NEW_inverse(x:M31)->M31{x.inv()}\n'
 # Actual emitted fixtures are compared with exact native observations, all lanes.
 fixture=receipt('NEW_L008',0)
 log=(E/'NEW_L008/stdout.log').read_text();literal=next(l for l in log.splitlines() if l.startswith('"{'))
 values=json.loads(json.loads(literal));assert values['0']=='assertionFailure' and len(values)==11
 native=[]
 for a,want in [('NEW_N001',0),('NEW_N002',101)]:
  r=receipt(a,want);native.append(r)
  assert r['env'].get('CARGO_NET_OFFLINE')=='true'
  graph=obj(E/(a+'-graph-check.json'));assert graph['graph_matches_frozen'] and graph['exact_frozen_selected_graph']
  features=next(p['features'] for p in graph['resolved_features_all_crates'] if p['name']=='aspis-core');assert features==['r0']
  lock=obj(E/(a+'-lock-check.json'));assert lock['unchanged'] and lock['before']==lock['after']==pins['lock_before']
  inputs=json.loads(lzma.decompress((E/(a+'_INPUTS.json.xz')).read_bytes()))
  assert inputs['NEW_src/crates/aspis-core/src/field.rs'].encode()==frozen
  assert inputs['NEW_src/crates/aspis-core/examples/NEW_inverse.rs']==(E/'NEW_native_inverse.rs').read_text()
  text=(E/a/'stdout.log').read_text();assert 'zero:assertionFailure' in text
  observed=dict(re.findall(r'^(\d+):(\d+)$',text,re.M))
  if not want:assert {k:int(v) for k,v in observed.items()}=={k:v for k,v in values.items() if k!='0'}
  else:assert 'assertion `left == right` failed' in text and observed=={'1':'1'}
 assert native[0]['source_hashes']==native[1]['source_hashes']
 proofs=[]
 for a,names in [('NEW_L006',['reducer','multiply','square_body','square_loop','square','emitted','cohort','zero']),('NEW_L007',['reference','result_state_effects','nonzero_calls'])]:
  r=receipt(a,0)
  for path,h in r['source_hashes'].items():assert sha(E/path)==h,('proof source drift',path)
  for line in r['print_axioms']:
   m=re.search(r'depends on axioms: \[([^\]]*)\]',line)
   if m:assert {name.strip() for name in m[1].split(',') if name.strip()} <= {'propext','Classical.choice','Quot.sound'}
   else:assert 'does not depend on any axioms' in line
  namespace='NEW_InverseAssociation' if a=='NEW_L006' else 'NEW_InverseComplete'
  for name in names:assert any("'"+namespace+'.'+name+"'" in line for line in r['print_axioms'])
  proofs.append(dict(attempt=a,source_hashes=r['source_hashes'],print_axioms=r['print_axioms']))
 return dict(method='D188 direct actual-body extraction with universal Lean association and finite native fidelity',domain='Every raw U32 word; zero assertionFailure retained',extraction='NEW_E003',native_pair=['NEW_N001','NEW_N002'],fixture='NEW_L008',proofs=proofs,slice_roots_status='OPEN',source_sha256=hashlib.sha256(frozen).hexdigest(),trust='P6/D188 option-A semantic transport retained; native fixtures are not universal arithmetic proofs',panic='Actual zero assertion mapped to emitted assertionFailure; no empty native panic I/O assertion',false_pass_quarantine=[],suspended_writable_static=[])
if __name__=='__main__':print(json.dumps(audit(),indent=1))
