from pathlib import Path
import json,subprocess,re,datetime
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s2h-20261023'
source='''import json,subprocess,re,datetime
text=subprocess.check_output(['ps','-eo','pid=,args='],text=True)
rows=[]
for line in text.splitlines():
 parts=line.strip().split(None,1)
 if len(parts)==2 and 'S2H_' in parts[1] and re.search(r'(?:^|/)(?:lean|lake|cargo-kani|kani-compiler|rustc|timeout)(?: |$)',parts[1]):rows.append(line.strip())
print(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'worker_proof_build_processes':rows,'qualification':'Read-only process inspection; other workers are not modified'}))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=source,text=True,capture_output=True,check=True)
x=json.loads(r.stdout);assert not x['worker_proof_build_processes'],x
(E/'S2H-final-host-state.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x))
