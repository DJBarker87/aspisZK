from pathlib import Path
import subprocess,json,base64,sys
E=Path(__file__).resolve().parent;a=sys.argv[1];B='/home/dombarker/project-offloads/codex-cx-slice-d-checkpoint-20261104'
code=f'''from pathlib import Path
import json,base64
b=Path({B!r});a={a!r};names=[str(p.relative_to(b)) for p in (b/a).rglob('*') if p.is_file()]+[a+'.json']+[str(p.relative_to(b)) for p in (b/'NGC_final_audit').rglob('*') if p.is_file()]
p=b/'NGC_LOADED_scan.jsonl'
if p.exists():names.append(str(p.relative_to(b)))
print(json.dumps({{n:base64.b64encode((b/n).read_bytes()).decode() for n in names}}))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True);assert r.returncode==0,r.stderr
for n,s in json.loads(r.stdout).items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(s))
r=json.loads((E/a/'receipt.json').read_text());done={json.loads(l).get('attempt') for l in (E/'NGC_ATTEMPTS.jsonl').read_text().splitlines()}
if a not in done:
 with (E/'NGC_ATTEMPTS.jsonl').open('a')as f:f.write(json.dumps(r)+'\n')
print(a,r['exit_status'],r['wall_seconds'],r['peak_rss_kib'],r['swaps'])
