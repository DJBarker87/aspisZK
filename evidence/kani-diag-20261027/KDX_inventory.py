from pathlib import Path
import json,re,hashlib,subprocess
E=Path(__file__).resolve().parent;root=E.parents[1]
rows=[];patches=[]
for name in subprocess.check_output(['git','ls-files','evidence'],cwd=root,text=True).splitlines():
 p=root/name
 if not p.is_file() or E in p.parents:continue
 if p.suffix=='.patch':
  t=p.read_text(errors='replace')
  if re.search(r'\b(?:LP[a-t]|NB[A-M]|NP6)_',t):patches.append(dict(path=str(p.relative_to(root)),sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
 if p.name!='receipt.json':continue
 try:d=json.loads(p.read_text())
 except:continue
 if d.get('exit_status',d.get('exit'))!=0:continue
 log=p.with_name('stdout.log')
 if not log.exists():continue
 t=log.read_text(errors='replace')
 hs=re.findall(r'Checking harness ([^\s.][^\n]*?)\.{3}',t)
 if not hs or not re.search(r'VERIFICATION:- SUCCESSFUL|successfully verified harnesses',t):continue
 if not any(re.search(r'\b(?:LP[a-t]|NB[A-M]|NP6)_',h) for h in hs):continue
 cmd=next((json.loads(l)['command'] for l in t.splitlines() if l.startswith('{') and '"command"' in l),d.get('command'))
 rows.append(dict(receipt=str(p.relative_to(root)),harnesses=hs,command=cmd,env=d.get('env'),source_hashes=d.get('source_hashes'),sources=d.get('sources'),deps=d.get('deps_fingerprint')))
(E/'KDX_PASS_INVENTORY.json').write_text(json.dumps(rows,indent=2)+'\n')
(E/'KDX_PATCH_INVENTORY.json').write_text(json.dumps(patches,indent=2)+'\n')
print(len(rows),'passing receipts',sum(len(x['harnesses']) for x in rows),'harness invocations',len(patches),'patches')
