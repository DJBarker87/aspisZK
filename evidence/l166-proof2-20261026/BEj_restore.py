"""Task-only sequential calls to the unchanged capped launcher; no launcher repair."""
from pathlib import Path
import json,subprocess,sys
P=Path(__file__).resolve().parent;R=P.parents[1]
plan=json.loads((P/'BEj_dependency_plan.json').read_text())
cache=json.loads((P/'BEj_cache_inventory.json').read_text())
paths=json.loads((P/'BEj_012.json').read_text())['env']['LEAN_PATH'].split(':')
HOST='dombarker@100.108.41.90'
failed=set();results=[];n=16
# Both prior prerequisite inventory errors happened before Lean; all receipt
# directories are actual compiler invocations, including failed elaborations.
def used():return len(list(P.glob('BEj_*/receipt.json')))
def present(m):
 script='from pathlib import Path\nroots='+repr(paths)+'\nm='+repr(m)+'\nprint(next((str(Path(r)/(m+".olean")) for r in roots if (Path(r)/(m+".olean")).is_file()),""))\n'
 return subprocess.check_output(['ssh',HOST,'python3'],input=script,text=True).strip()
def blocked(m,seen=None):
 seen=set() if seen is None else seen
 if m in seen:return False
 seen.add(m)
 return m in failed or any(blocked(d,seen) for d in plan['modules'].get(m,{}).get('imports',[]))
for m in plan['order']:
 if used()>=100:break
 if cache[m] is not None:continue
 if present(m):
  results.append({'module':m,'status':'cached by concurrent job; not rerun'});continue
 if blocked(m):
  results.append({'module':m,'status':'blocked by failed predecessor; not run'});continue
 print(f'Attempt {n}: {m}, {used()}/100 compiler attempts used',flush=True)
 logfile=P/f'BEj_{n:03}-driver.log'
 cmd=[sys.executable,str(P/'BEj_compile.py'),str(n),m]
 if not m.startswith('BEj_'):cmd.append('--dependency')
 with logfile.open('w') as log:proc=subprocess.run(cmd,cwd=R,stdout=log,stderr=subprocess.STDOUT)
 receipt=P/f'BEj_{n:03}'/'receipt.json'
 if receipt.exists():
  r=json.loads(receipt.read_text());print(f"  exit={r['exit_status']}, wall={r['wall_seconds']}, RSS={r['peak_rss_kib']}",flush=True)
  results.append({'attempt':n,'module':m,'status':r['exit_status']})
  if r['exit_status']!=0:failed.add(m)
 else:
  print('  Launcher failure before compile; stopping under local rule 5.',flush=True)
  results.append({'attempt':n,'module':m,'status':'launcher failure before compile','exit':proc.returncode})
  (P/'BEj_restore_results.json').write_text(json.dumps(results,indent=2)+'\n')
  sys.exit(proc.returncode or 1)
 (P/'BEj_restore_results.json').write_text(json.dumps(results,indent=2)+'\n')
 n+=1
print(f'Finished: {used()}/100 compiler attempts',flush=True)
