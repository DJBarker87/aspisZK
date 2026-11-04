"""Add-only continuation: immutable NEX validation is always replayed first."""
from pathlib import Path
import sys,json,copy,argparse,hashlib,re
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent
sys.path.insert(0,str(E.parent/'slice-s-compose8-20261104'))
import NEX_validate as inherited
sha=lambda data:hashlib.sha256(data).hexdigest()
read=inherited.read
def native(a,positive):
 r=read(E/a/'receipt.json');c=read(E/(a+'.json'))
 assert r['kind']=='kani' and r['source_revision'] and int(r['swaps'])==0
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert c['env']['CARGO_NET_OFFLINE']=='true' and c['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert c['native_command'][0]=='/home/dombarker/.cargo/bin/cargo-kani'
 assert '--locked' not in c['native_command'] and c['native_command'][c['native_command'].index('--harness-timeout')+1]=='90s'
 assert r['exit_status']==(0 if positive else 1)
 assert all(r[k]==v for k,v in c.items())
 ad=read(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed'] is True
 assert read(E/(a+'-graph-check.json'))['exact_LPm_graph'] is True
 from NEY_frozen_identity import check as frozen_identity
 assert read(E/(a+'-frozen-identity.json'))==frozen_identity(a)
 assert read(E/(a+'-lock-check.json'))['unchanged'] is True
 assert read(E/(a+'-rule16-check.json'))['no_writable_static'] is True
 assert not read(E/(a+'-source-check.json'))['errors']
 assert c['copy_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 log=(E/a/'stdout.log').read_text()
 assert ('VERIFICATION:- SUCCESSFUL' in log) is positive
 assert positive or 'Failed Checks:' in log
 assert 'timed out' not in log.lower()
 archive=E/(a+'-inputs.json')
 snapshots=read(archive)[a] if Path(str(archive)+'.xz').exists() else read(E/'NEY_SOURCE_HISTORY.json')[a]
 assert set(snapshots)==set(r['source_hashes'])
 assert all(sha(s.encode())==r['source_hashes'][n] for n,s in snapshots.items())
 for n in ['NEY_native_contracts.patch','NEY_oracle.patch']:assert snapshots[n]==(E/(a+'-'+n)).read_text()
 source=snapshots['NEY_native_contracts.patch']
 assert not any(s in source.replace('AtomicStatementError','') for s in ['static mut','stub_verified','UnsafeCell','Atomic','transmute'])
 assert not re.search(r'\bstatic\s+mut\b|\b(?:Cell|RefCell|UnsafeCell)\b',source)
 features={p['name']:set(p['features']) for p in read(E/(a+'-metadata-pin.json'))['features_all_crates']}
 assert set(c['required_statement_features'])<=features['aspis-statement']
 if 'program_features' in c:
  assert {'pool-adapter','private-leaf-salts'}<=features['aspis-r1-cost-probe-program']
  assert not {'no-entrypoint','cu-profiling'}&features['aspis-r1-cost-probe-program']
  assert {'default','private-leaf-salts','optimized-terminal','program-build'}<=features['aspis-r1-cost-probe']
 return snapshots

def baseline():
 return inherited.compose(inherited.read(R/'evidence/native-ledger3-20261029/NDT_LEDGER.json'),inherited.read(inherited.E/'NEX_LEDGER_DELTA.json'),inherited.read(inherited.E/'NEX_REVIEWED_CERTIFICATES.json'))
def certificate(c,subject,base):
 if c is None:return False
 try:
  assert c['subject']==subject and c['frozen_revision']==base['frozen_revision']
  assert c['semantic_review_sha256']==sha(json.dumps({k:w for k,w in c.items() if k!='semantic_review_sha256'},sort_keys=True).encode())
  for key in ['exact_callsite','canonical_carrier','same_arguments','same_prestate','same_result','same_ordered_effects','native_frame_complete','callee_domain_established']:assert c[key] is True
  assert c['inner_hypotheses_remaining']==[]
  assert c['trust_classification']=='P6/D188 option A reclassification'
  assert c['support'] and c['domain_theorems'] and c['physical_theorems']
  for pin in c['support']:inherited.artifact(pin)
  for theorem in c['domain_theorems']+c['physical_theorems']:assert __import__("NED_validate").theorem(theorem)
  from NEY_bridge_checks import check
  from NEY_residual_checks import FUNCTIONS,check as residual_check
  assert (residual_check if c['native_certificate']['function'] in FUNCTIONS else check)(c,base)
  return True
 except (AssertionError,KeyError,TypeError,ValueError,OSError,ImportError):
  import os,traceback
  if os.environ.get('NEY_DEBUG'):traceback.print_exc()
  return False
def compose(base,packet):
 assert packet['inherits']=='evidence/slice-s-compose8-20261104/NEX_LEDGER_DELTA.json.xz'
 result=copy.deepcopy(base)
 # No generic Boolean or arbitrary certificate can promote a row. New shapes
 # need their own frozen-source/native/Lean checker and bottom-up domain join.
 if packet.get('NEY_certificates'):
  from NEY_bridge_checks import compose_additions
  result=compose_additions(base,result,packet,sys.modules[__name__])
  from NEY_residual_checks import compose as residual_compose
  result=residual_compose(base,result,packet,sys.modules[__name__])
 assert result['trust_rows']==base['trust_rows']
 return result
def main():
 a=argparse.ArgumentParser();a.add_argument('--write',type=Path);args=a.parse_args()
 out=compose(baseline(),json.loads((E/'NEY_LEDGER_DELTA.json').read_text()))
 report=inherited.inherited.summary(out)
 if args.write:args.write.write_text(json.dumps(report,indent=1)+'\n')
 print(json.dumps(report,indent=1))
if __name__=='__main__':main()
