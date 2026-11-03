"""Additive NDT continuation: imported acceptance and explicit domain checks."""
from pathlib import Path
import sys,json,argparse,hashlib
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent
sys.path.insert(0,str(E.parent/'slice-s-compose6-20261102'))
import NEQ_validate as predecessor
from NEQ_inputs import read
BASE_CERTIFICATE=predecessor.certificate
inherited=predecessor.inherited

def certificate(c,expected,ledger,reviewed):
 # No fallback can bypass a predecessor gate.
 if not BASE_CERTIFICATE(c,expected,ledger,reviewed):return False
 # Every NEQ execution certificate already has these checks. Repeat the
 # explicit subject and native-frame bindings for all later continuations.
 if c.get('id','').startswith(('NEQ_','NEU_')):
  import NEJ_validate
  if not NEJ_validate.call_domain(c,expected,ledger):return False
 return True

def compose(base,packet,reviewed):
 previous=predecessor.certificate
 try:
  predecessor.certificate=certificate
  return predecessor.compose(base,packet,reviewed)
 finally:predecessor.certificate=previous

def summary(out):
 import NEJ_validate
 return NEJ_validate.summary(out)

def main():
 a=argparse.ArgumentParser();a.add_argument('--write',type=Path);args=a.parse_args()
 packet=read(E.parent/'slice-s-compose6-20261102/NEQ_LEDGER_DELTA.json')
 reviewed=read(E.parent/'slice-s-compose6-20261102/NEQ_REVIEWED_CERTIFICATES.json')
 out=compose(read(R/'evidence/native-ledger3-20261029/NDT_LEDGER.json'),packet,reviewed)
 result=summary(out)
 if args.write:args.write.write_text(json.dumps(result,indent=1)+'\n')
 print(json.dumps(result,indent=1))
if __name__=='__main__':main()
