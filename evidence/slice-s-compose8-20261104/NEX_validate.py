"""Additive NDT/NEU validation. Native certificates never bypass baseline gates."""
from pathlib import Path
import sys,json,hashlib,copy,argparse,lzma
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent
sys.path.insert(0,str(E.parent/'slice-s-compose7-20261103'))
import NEU_validate as inherited
sha=lambda b:hashlib.sha256(b).hexdigest()
def read(p):
 p=Path(p)
 if p.is_file():return json.loads(p.read_text())
 raw=lzma.decompress(Path(str(p)+'.xz').read_bytes());assert sha(raw)==Path(str(p)+'.sha256').read_text().strip();return json.loads(raw)
def artifact(r):
 p=R/r['path'];assert p.is_file() and sha(p.read_bytes())==r['sha256'];return p

def native(a,positive):
 r=read(E/a/'receipt.json');c=read(E/(a+'.json'))
 assert r['exit_status']==(0 if positive else 1)
 assert all(r[k]==v for k,v in c.items())
 ad=read(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed'] is True
 assert read(E/(a+'-graph-check.json'))['exact_LPm_graph'] is True
 assert read(E/(a+'-lock-check.json'))['unchanged'] is True
 assert read(E/(a+'-rule16-check.json'))['no_writable_static'] is True
 assert not read(E/(a+'-source-check.json'))['errors']
 assert c['copy_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 log=(E/a/'stdout.log').read_text()
 assert ('VERIFICATION:- SUCCESSFUL' in log) is positive
 assert positive or 'Failed Checks:' in log
 assert 'timed out' not in log.lower()
 archive=E/(a+'-inputs.json')
 snapshots=read(archive)[a] if Path(str(archive)+'.xz').exists() else read(E/'NEX_SOURCE_HISTORY.json')[a]
 assert set(snapshots)==set(r['source_hashes'])
 assert all(sha(s.encode())==r['source_hashes'][n] for n,s in snapshots.items())
 for n in ['NEX_native_contracts.patch','NEX_oracle.patch']:assert snapshots[n]==(E/(a+'-'+n)).read_text()
 source=snapshots['NEX_native_contracts.patch']
 assert not any(s in source for s in ['static mut','stub_verified','UnsafeCell','Atomic','transmute'])
 features={p['name']:set(p['features']) for p in read(E/(a+'-metadata-pin.json'))['features_all_crates']}
 assert set(c['required_statement_features'])<=features['aspis-statement']
 return snapshots

def certificate(c,subject,ledger,reviewed):
 try:
  assert c and c['subject']==subject and c['frozen_revision']==ledger['frozen_revision']
  function=c['native_certificate']['function']
  rows=[r for r in ledger['rows'] if r['function']==function]
  allowed={function}
  for row in rows:
   allowed.update(function+'::'+h['name'] for h in row['named_hypotheses'])
   allowed.update(function+' -> '+o['callee'] if 'callee' in o else o['id'] for o in row['caller_domain_obligations'])
  assert subject in allowed
  assert c['semantic_review_sha256']==reviewed[subject]==sha(json.dumps({k:v for k,v in c.items() if k!='semantic_review_sha256'},sort_keys=True).encode())
  assert c['inner_hypotheses_remaining']==[] and c['new_trust_rows']==[]
  assert c['trust_classification']=='P6/D188 option A reclassification'
  for k in ['exact_callsite','canonical_carrier','same_arguments','same_prestate','same_result','same_ordered_effects','native_frame_complete','callee_domain_established']:assert c[k] is True
  assert c['domain_theorems'] and c['physical_theorems']
  for t in c['domain_theorems']+c['physical_theorems']:assert inherited.inherited.theorem(t)
  for r in c['support']:artifact(r)
  assert c['native_certificate']['complete'] is True
  from NEX_bridge_checks import check
  assert check(c,ledger)
  return True
 except (AssertionError,KeyError,TypeError,ValueError,OSError,ImportError):return False

def compose(base,packet,reviewed):
 prior=copy.deepcopy(packet)
 for group in ['roots','members','edges','hypotheses','externals','inventory_edges']:
  prior[group]={k:c for k,c in prior.get(group,{}).items() if not c.get('id','').startswith('NEX_')}
 prior.pop('NEX_native_bridge_additions',None)
 result=inherited.compose(base,prior,reviewed)
 # No new status is admitted unless every independent checker has passed.
 from NEX_bridge_checks import compose_additions
 return compose_additions(base,result,packet,reviewed,sys.modules[__name__])
def main():
 a=argparse.ArgumentParser();a.add_argument('--write',type=Path);args=a.parse_args()
 out=compose(read(R/'evidence/native-ledger3-20261029/NDT_LEDGER.json'),read(E/'NEX_LEDGER_DELTA.json'),read(E/'NEX_REVIEWED_CERTIFICATES.json'))
 result=inherited.summary(out)
 if args.write:args.write.write_text(json.dumps(result,indent=1)+'\n')
 print(json.dumps(result,indent=1))
if __name__=='__main__':main()
