from pathlib import Path
import subprocess,json,re,hashlib
E=Path(__file__).resolve().parent;R=E.parent.parent
code="""from pathlib import Path
import json
b=Path('/home/dombarker/project-offloads'); roots=[b/'codex-cx-slice-s-compose-20261029/NED_objects',b/'codex-cx-slice-s-compose-cache-20261029',b/'codex-cx-sound-int2-20261025',b/'codex-cx-sound-int2-20261025/objects']
print(json.dumps({str(p.relative_to(root))[:-6].replace('/','.'):str(p) for root in reversed(roots) for p in root.rglob('*.olean') if root.name not in ['codex-cx-sound-int2-20261025'] or p.parent==root}))
"""
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0
objects=json.loads(r.stdout);files=subprocess.check_output(['git','ls-files'],text=True).splitlines();mapping={}
for base in ['docs/research/100bit-spend-path-20261013/lean/','lean/']:
 for p in files:
  if p.startswith(base) and p.endswith('.lean'):mapping[p[len(base):-5].replace('/','.')]=p
seen=set();plan=[];sources={};missing=[]
def visit(n):
 if n in seen or n in objects:return
 seen.add(n)
 if n.startswith(('Init','Lean','Std')):return
 if n not in mapping:missing.append(n);return
 path=mapping[n];src=subprocess.check_output(['git','show','HEAD:'+path],text=True)
 for dep in re.findall(r'^import\s+([\w.]+)',src,re.M):visit(dep)
 sources[n]=dict(path=path,sha256=hashlib.sha256(src.encode()).hexdigest(),source=src);plan.append(n)
for n in ['NBP_DigestEncode','NBP_TransferEncode','NBP_WithdrawalEncode']:visit(n)
(E/'NED_UNCHANGED_BUILD_PLAN.json').write_text(json.dumps(dict(plan=plan,missing=missing,sources=sources),indent=1)+'\n');print(len(plan),plan,'missing',missing)
