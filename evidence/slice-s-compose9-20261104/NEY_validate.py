"""Add-only continuation: immutable NEX validation is always replayed first."""
from pathlib import Path
import sys,json,copy,argparse,hashlib
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent
sys.path.insert(0,str(E.parent/'slice-s-compose8-20261104'))
import NEX_validate as inherited
sha=lambda data:hashlib.sha256(data).hexdigest()
def baseline():
 return inherited.compose(inherited.read(R/'evidence/native-ledger3-20261029/NDT_LEDGER.json'),inherited.read(inherited.E/'NEX_LEDGER_DELTA.json'),inherited.read(inherited.E/'NEX_REVIEWED_CERTIFICATES.json'))
def certificate(c,subject,base):
 try:
  assert c['subject']==subject and c['frozen_revision']==base['frozen_revision']
  for key in ['exact_callsite','canonical_carrier','same_arguments','same_prestate','same_result','same_ordered_effects','native_frame_complete','callee_domain_established']:assert c[key] is True
  assert c['inner_hypotheses_remaining']==[]
  assert c['trust_classification']=='P6/D188 option A reclassification'
  assert c['support'] and c['domain_theorems'] and c['physical_theorems']
  for pin in c['support']:inherited.artifact(pin)
  for theorem in c['domain_theorems']+c['physical_theorems']:assert inherited.inherited.inherited.theorem(theorem)
  from NEY_bridge_checks import check
  assert check(c,base)
  return True
 except (AssertionError,KeyError,TypeError,ValueError,OSError,ImportError):return False
def compose(base,packet):
 result=copy.deepcopy(base)
 # No generic Boolean or arbitrary certificate can promote a row. New shapes
 # need their own frozen-source/native/Lean checker and bottom-up domain join.
 if packet.get('NEY_certificates'):
  from NEY_bridge_checks import compose_additions
  result=compose_additions(base,result,packet,sys.modules[__name__])
 assert result['trust_rows']==base['trust_rows']
 return result
def main():
 a=argparse.ArgumentParser();a.add_argument('--write',type=Path);args=a.parse_args()
 out=compose(baseline(),json.loads((E/'NEY_LEDGER_DELTA.json').read_text()))
 report=inherited.inherited.summary(out)
 if args.write:args.write.write_text(json.dumps(report,indent=1)+'\n')
 print(json.dumps(report,indent=1))
if __name__=='__main__':main()
