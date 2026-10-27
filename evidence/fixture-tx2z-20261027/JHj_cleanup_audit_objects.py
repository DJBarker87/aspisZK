from pathlib import Path
import json,subprocess,shlex
P=Path(__file__).resolve().parent
objects=json.loads((P/'JHj_FINAL_HOST_OBJECTS.json').read_text())
selected={n:r for n,r in objects.items() if n.startswith('JHj_Audit') or n in ['JHj_InitialAudit','JHj_EmissionAudit','JHj_TopAudit']}
code='''import json,sys,hashlib\nfrom pathlib import Path\nx=json.load(sys.stdin);removed=[]\nfor name,row in x.items():\n for item in row['objects']:\n  p=Path(item['path']);assert p.parent==Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025') and p.name.startswith(name+'.olean'),str(p)\n  assert hashlib.sha256(p.read_bytes()).hexdigest()==item['sha256'],str(p)\n  p.unlink();removed.append(str(p))\nlive=[]\nfor p in Path('/proc').iterdir():\n if not p.name.isdigit():continue\n try:a=(p/'cmdline').read_bytes().decode(errors='replace').split('\\0')\n except (FileNotFoundError,PermissionError,ProcessLookupError):continue\n if a and (Path(a[0]).name=='lean' or (len(a)>1 and Path(a[1]).name=='S2W_lean_host.py')) and any(Path(s).name.startswith('JHj_') for s in a):live.append(dict(pid=p.name,args=a))\nprint(json.dumps(dict(removed=removed,live_proof_processes=live),indent=2));assert not live'''
r=subprocess.run(['ssh','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(selected),capture_output=True,text=True)
r.check_returncode();result=json.loads(r.stdout)
(P/'JHj_HOST_CLEANUP.json').write_text(r.stdout)
for name,row in objects.items():
 for item in row['objects']:item['audit_scratch_removed']=name in selected
(P/'JHj_FINAL_HOST_OBJECTS.json').write_text(json.dumps(objects,indent=2)+'\n')
print(len(selected),'own audit roots removed;',len(objects)-len(selected),'canonical proof cache modules retained; no live proof process')
