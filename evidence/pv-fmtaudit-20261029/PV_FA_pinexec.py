from pathlib import Path
import sys,json,hashlib,subprocess
H=Path('/home/dombarker/project-offloads/codex-pv-fmtaudit-20261029');id=int(sys.argv[1]);module=sys.argv[2];env=json.loads((H/'pinned.json').read_text());src=H/'pinned-source/backends/lean'/(module+'.lean');out=H/'pinned-objects'/(module+'.olean');resolution=[]
for x in json.loads((H/'input-external-object-manifest.json').read_text()):
 top=x['module'].split('/')[0];roots=[Path(v)for v in env['LEAN_PATH'].split(':')];root=next(r for r in roots if(r/top).exists()or(r/(top+'.olean')).exists());q=root/(x['module']+'.olean');resolution.append(dict(module=x['module'],path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest()if q.exists()else None))
(H/('pinned-resolution-pre-'+str(id)+'.json')).write_text(json.dumps(resolution,indent=1))
cmd=[env['LEAN'],'--root='+str(H/'pinned-source/backends/lean'),'-M7000','-j1','-DElab.async=false','-o',str(out),str(src)]
r=subprocess.run(cmd);result=dict(attempt=id,module=module,command=cmd,source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),exit_status=r.returncode,output_sha256=hashlib.sha256(out.read_bytes()).hexdigest()if r.returncode==0 else None,preflight_sha256=hashlib.sha256((H/('pinned-resolution-pre-'+str(id)+'.json')).read_bytes()).hexdigest(),root_correction='explicit --root preserves Aeneas module-private names; preflight inside capped scope')
(H/('pincompile-artifact-'+str(id)+'.json')).write_text(json.dumps(result,indent=1));print(json.dumps(result),flush=True);sys.exit(r.returncode)
