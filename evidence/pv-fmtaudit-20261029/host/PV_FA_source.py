from pathlib import Path
import subprocess,tarfile,io,json,hashlib,difflib,shutil
H=Path('/home/dombarker/project-offloads/codex-pv-fmtaudit-20261029');repo=H.parent/'codex-pv-cx-20261029/resume-ae1/aeneas';pin='b59d5188c082f704a418c7cb4e52ad69328002d1';D=H/'pinned-source';D.mkdir(exist_ok=False)
data=subprocess.check_output(['git','-C',str(repo),'archive',pin,'backends/lean'])
with tarfile.open(fileobj=io.BytesIO(data))as t:t.extractall(D,filter='data')
subprocess.run(['git','apply','--include=backends/lean/**',str(H/'aeneas-b59d5188-lean432.patch')],cwd=D,check=True)
M=json.loads((H/'input-external-object-manifest.json').read_text());out=[];overlay=H/'pinned-objects';overlay.mkdir()
for x in M:
 if not x['module'].startswith(('Aeneas/','AeneasMeta/'))and x['module']not in ['Aeneas','AeneasMeta']:continue
 mod=x['module'];src=D/'backends/lean'/(mod+'.lean'); shared=H.parent/'aspis-joint-20261019/sources'/(mod+'.lean')
 row=dict(module=mod,source_path=str(src),source_sha256=hashlib.sha256(src.read_bytes()).hexdigest()if src.exists()else None,source_blob=subprocess.run(['git','-C',str(repo),'rev-parse',pin+':backends/lean/'+mod+'.lean'],capture_output=True,text=True).stdout.strip())
 if shared.exists():
  row['shared_source_sha256']=hashlib.sha256(shared.read_bytes()).hexdigest();row['shared_differs']=shared.read_bytes()!=src.read_bytes()
  if row['shared_differs']:(H/('source-diff-'+mod.replace('/','_')+'.patch')).write_text(''.join(difflib.unified_diff(src.read_text().splitlines(True),shared.read_text().splitlines(True),fromfile='pinned/'+mod,tofile='shared/'+mod)))
 # A namespace-complete plain-copy overlay, never linked to a cohort.
 q=Path(x['path']);dest=overlay/(mod+'.olean');dest.parent.mkdir(parents=True,exist_ok=True)
 assert hashlib.sha256(q.read_bytes()).hexdigest()==x['object_sha256'];shutil.copyfile(q,dest)
 for suffix in ['.private','.server']:
  c=Path(str(q)+suffix)
  if c.exists():shutil.copyfile(c,Path(str(dest)+suffix))
 ir=q.with_suffix('.ir')
 if ir.exists():shutil.copyfile(ir,dest.with_suffix('.ir'))
 out.append(row)
(H/'source-inventory.json').write_text(json.dumps(out,indent=1));print('source modules',len(out),'shared differences',[(x['module'],x['shared_differs'])for x in out if 'shared_differs'in x])
# The original Fmt file is compiled separately as an unmodified source, then inspected.
env=json.loads((H/'authority.json').read_text());env['LEAN_PATH']=str(overlay)+':'+env['LEAN_PATH'];(H/'pinned.json').write_text(json.dumps(env,indent=2))
