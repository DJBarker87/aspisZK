"""Switch only the batch inputs in this job's one pinned host source workspace."""
from pathlib import Path
import subprocess,json,hashlib,sys
H='dombarker@100.108.41.90';D='/home/dombarker/project-offloads/codex-pv-batch2-20261027';who=sys.argv[1];assert who in ['baseline','candidate']
rev='73070ddd512bc4e79edfc0db714fb64dc74e87b8' if who=='baseline' else '5b92d4aa185486cc735c0a3eb75a3024171ca482'
files=subprocess.check_output(['git','diff','--name-only','73070ddd51','5b92d4aa18','--','crates/'],text=True).splitlines();manifest=[]
for f in files:
 r=subprocess.run(['git','show',rev+':'+f],capture_output=True)
 if r.returncode:continue # baseline has no host copy declarations; extra unreferenced files remain
 manifest.append(dict(path=f,sha256=hashlib.sha256(r.stdout).hexdigest()))
 subprocess.run(['ssh',H,'cat > '+D+'/candidate/src/'+f],input=r.stdout,check=True)
subprocess.run(['ssh',H,'cat > '+D+'/candidate/source-revision.txt'],input=(rev+'\n').encode(),check=True)
subprocess.run(['ssh',H,'cat > '+D+'/'+who+'-inputs.json'],input=json.dumps(dict(revision=rev,files=manifest,extra_unreferenced_candidate_modules=who=='baseline'),indent=2).encode(),check=True)
