"""Additive NDT continuation: imported acceptance and explicit domain checks."""
from pathlib import Path
import sys,json,argparse,hashlib,copy,subprocess
from functools import lru_cache
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent
sys.path.insert(0,str(E.parent/'slice-s-compose6-20261102'))
import NEQ_validate as predecessor
from NEU_inputs import read
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

@lru_cache(maxsize=None)
def frozen_source(function):
 return subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+function.split('::',1)[0]],cwd=R,text=True)

def compose(base,packet,reviewed):
 inherited_packet=copy.deepcopy(packet)
 for group in ['roots','members','edges','hypotheses','externals','inventory_edges']:
  inherited_packet[group]={k:c for k,c in inherited_packet.get(group,{}).items() if not c.get('id','').startswith('NEU_')}
 previous=predecessor.certificate
 try:
  predecessor.certificate=certificate
  out=predecessor.compose(base,inherited_packet,reviewed)
 finally:predecessor.certificate=previous
 import NEU_bridge_checks
 return NEU_bridge_checks.compose(base,out,packet,reviewed,sys.modules[__name__])

def summary(out):
 import NEJ_validate
 s=NEJ_validate.summary(out)
 s["native_admissions"]=out.get("NEU_native_admissions",{})
 s["closed_row_count"]=len(s["slice_closed"])
 s["root_closed_count"]=sum(all(x=="CLOSED" for x in rows) for rows in s["roots"].values())
 return s

def main():
 a=argparse.ArgumentParser();a.add_argument('--write',type=Path);args=a.parse_args()
 packet=read(E/'NEU_LEDGER_DELTA.json')
 reviewed=read(E/'NEU_REVIEWED_CERTIFICATES.json')
 out=compose(read(R/'evidence/native-ledger3-20261029/NDT_LEDGER.json'),packet,reviewed)
 result=summary(out)
 if args.write:args.write.write_text(json.dumps(result,indent=1)+'\n')
 print(json.dumps(result,indent=1))
if __name__=='__main__':main()
