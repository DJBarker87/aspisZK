"""Add-only NDT continuation. Inherited NEY checks run unchanged first."""
from pathlib import Path
import sys,json,copy,argparse,hashlib
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent
sys.path.insert(0,str(E.parent/'slice-s-compose9-20261104'))
import NEY_validate as inherited
read=inherited.read
sha=lambda s:hashlib.sha256(s).hexdigest()
def baseline():
 return inherited.compose(inherited.baseline(),read(inherited.E/'NEY_LEDGER_DELTA.json'))
def certificate(c,subject,base):
 if c is None:return False
 try:
  assert c['subject']==subject and c['frozen_revision']==base['frozen_revision']
  assert c['semantic_review_sha256']==sha(json.dumps({k:w for k,w in c.items() if k!='semantic_review_sha256'},sort_keys=True).encode())
  assert c['inner_hypotheses_remaining']==[]
  assert c['trust_classification']=='P6/D188 option A reclassification'
  for key in ['exact_callsite','canonical_carrier','same_arguments','same_prestate','same_result','same_ordered_effects','native_frame_complete','callee_domain_established']:assert c[key] is True
  assert c['support'] and c['domain_theorems'] and c['physical_theorems']
  for pin in c['support']:inherited.inherited.artifact(pin)
  for theorem in c['domain_theorems']+c['physical_theorems']:assert __import__('NED_validate').theorem(theorem)
  from NFD_bridge_checks import check
  assert check(c,base)
  return True
 except (AssertionError,KeyError,TypeError,ValueError,OSError,ImportError):
  return False

def compose(base,packet):
 assert packet['inherits']=='evidence/slice-s-compose9-20261104/NEY_LEDGER_DELTA.json'
 result=copy.deepcopy(base)
 if packet.get('NFD_certificates'):
  from NFD_bridge_checks import compose_additions
  result=compose_additions(base,result,packet,sys.modules[__name__])
 assert result['trust_rows']==base['trust_rows']
 return result

def main():
 p=argparse.ArgumentParser();p.add_argument('--write',type=Path);a=p.parse_args()
 out=compose(baseline(),read(E/'NFD_LEDGER_DELTA.json'))
 report=inherited.inherited.inherited.summary(out)
 if a.write:a.write.write_text(json.dumps(report,indent=1)+'\n')
 print(json.dumps(report,indent=1))
if __name__=='__main__':main()
