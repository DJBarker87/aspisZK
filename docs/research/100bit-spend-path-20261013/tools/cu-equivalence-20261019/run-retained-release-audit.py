from pathlib import Path
from concurrent.futures import ProcessPoolExecutor
import json,subprocess,sys,time,os,tempfile
repo=Path(__file__).resolve().parents[5];area=repo/'docs/research/100bit-spend-path-20261013';tool=area/'tools/cu-equivalence-20261019';ev=area/'evidence/cu-equivalence-20261019'
revision=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip()
names=['retained-composition-tx1','retained-composition-dots','retained-composition-weights','retained-input-bindings','retained-dots-canonical-composition','retained-claim-binding','retained-resume-weights','retained-finish-relation','retained-finish-dot-binding','retained-query-prefix-final']
def run(name):
 cmd=[sys.executable,str(tool/('check-'+name+'.py'))]
 if name in ['retained-input-bindings','retained-dots-canonical-composition','retained-query-prefix-final']:cmd+=['--check']
 start=time.monotonic()
 with tempfile.TemporaryFile() as out:
  p=subprocess.Popen(cmd,cwd=repo,stdout=out,stderr=subprocess.STDOUT)
  _,status,u=os.wait4(p.pid,0);p.returncode=os.waitstatus_to_exitcode(status);out.seek(0);result=out.read().decode(errors='replace')
 return dict(name=name,command=cmd,revision=revision,features='metadata/source/receipt audit only',exit=p.returncode,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss,process_swaps=u.ru_nswap,print_axioms='N/A: audit process; referenced Lean certificates contain exact outputs',output=result)
if __name__=='__main__':
 previous=[]
 if '--retry-failed' in sys.argv:
  old=ev/'RETAINED-COMPOSITION-RELEASE-AUDIT.json';previous=json.loads(old.read_text())
  (ev/'RETAINED-COMPOSITION-RELEASE-AUDIT-DIAGNOSTIC.json').write_text(old.read_text())
  names=[x['name']for x in previous if x['exit']!=0]
 with ProcessPoolExecutor(max_workers=3) as pool:fresh=list(pool.map(run,names))
 r=[x for x in previous if x['exit']==0]+fresh
 (ev/'RETAINED-COMPOSITION-RELEASE-AUDIT.json').write_text(json.dumps(r,indent=2)+'\n')
 for x in r:print(x['name'],x['exit'],round(x['wall_seconds'],2),x['output'][-450:])
 assert all(x['exit']==0 for x in r)
