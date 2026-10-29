from pathlib import Path
import json,hashlib,subprocess,sys,os,re
D=Path('/home/dombarker/project-offloads/codex-pv-mfb-20261029');f=json.load(open(D/'dlib-preflight-input.json'));sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
row=sys.argv[1];attempt=int(sys.argv[2]);assert 69600<=attempt<=69699
r=next(r for r in json.load(open(D/'request.json')) if r['id']==row);cs=r['closing'];env=f['environment'];roots=[Path(x) for x in env['LEAN_PATH'].split(':')];seen={}
# Corrected h4 preflight: all transitive external objects, before Lean starts.
ext=json.load(open(D/'external-object-manifest.json'))
for rec in ext:
 m=rec['module'].replace('.','/')
 ep=next((rt/(m+'.olean') for rt in roots if (rt/(m+'.olean')).exists()),None)
 assert ep and sha(ep)==rec['object_sha256'],(m,'h4 external mismatch',str(ep))
external_checked=len(ext)
def visit(m):
 m=m.replace('.','/')
 if m in seen:return
 j=f['source_closure'][m];p=next((rt/(m+'.olean') for rt in roots if (rt/(m+'.olean')).exists()),None);assert p,(m,'missing')
 if j.get('external'):assert sha(p)==j['object_sha256'],(m,'external mismatch');seen[m]=dict(path=str(p),sha256=sha(p),external=True);return
 rec=f['project'][m];assert str(p)==rec['object_path'] and sha(p)==rec['object_sha256'],(m,'object mismatch')
 sp=Path('/home/dombarker/project-offloads/codex-pv-dlib-20261028/lean-sources')/(m+'.lean');assert sha(sp)==j['source_sha256']==j['head_sha256'],(m,'source mismatch')
 seen[m]=dict(source=j,object_path=str(p),object_sha256=sha(p))
 for dep in j['imports']:visit(dep)
# Include the existing final audit's whole source closure. This binds every audit dependency before any compile.
for m in f['roots']:visit(m)
text='import '+cs['module']+'\n#check '+cs['theorem']+'\n#print axioms '+cs['theorem']+'\n'
O=D/('lean-'+str(attempt));O.mkdir(exist_ok=True);src=D/'sources'/('PV_MF_'+row+'.lean');src.parent.mkdir(exist_ok=True);src.write_text(text);ss=sha(src)
for q in D.glob('lean-*/result.json'):
 old=json.load(open(q));assert not(old.get('elaboration_failed') and old['source_sha256']==ss),'unchanged failed source'
(O/'preflight.json').write_text(json.dumps(dict(row=row,external_transitive_objects_checked=external_checked,external_manifest_sha256=sha(D/'external-object-manifest.json'),cohort_environment=env,toolchain=env['LEAN_GITHASH'],current_revision=f['current_revision'],imports=seen,source_sha256=ss),indent=2))
out=D/'objects';out.mkdir(exist_ok=True);ep=D/'dlib-env-J.json';ep.write_text(json.dumps(env))
cmd=['python3','/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py',str(ep),str(out),str(src.parent),str(out/('PV_MF_'+row+'.olean')),str(src),'7000']
a=subprocess.run(cmd,capture_output=True,text=True);(O/'lean-output.log').write_text(a.stdout+a.stderr)
(O/'result.json').write_text(json.dumps(dict(row=row,attempt=attempt,preflight_version='complete-h4',exit=a.returncode,source_sha256=ss,source_revision=f['current_revision'],elaboration_failed=a.returncode!=0,axioms=re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",a.stdout+a.stderr,re.S)),indent=2));print(a.stdout+a.stderr);sys.exit(a.returncode)
