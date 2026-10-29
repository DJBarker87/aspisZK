"""Read-only requested extension inventory; does not authorize imports or run Lean."""
import pathlib,json,hashlib,re,subprocess
root=pathlib.Path('/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal')
auth_path=pathlib.Path('/home/dombarker/project-offloads/codex-pv-replay-20261027/evidence/external-object-manifest.json')
auth={v['module'].replace('/','.'):v for v in json.loads(auth_path.read_text())}
packages=['mathlib','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','Cli']
roots=[root/'.lake/packages'/p for p in packages]
roots.append(pathlib.Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/src/lean'))
seen={};missing=[]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def visit(m):
 if m in seen:return
 if m in auth:
  v=auth[m];p=pathlib.Path(v['path']);seen[m]=dict(module=m,authority='existing h4',path=str(p),sha256=sha(p),expected=v['object_sha256'])
  return
 p=next((r/(m.replace('.','/')+'.lean') for r in roots if (r/(m.replace('.','/')+'.lean')).is_file()),None)
 if p is None:missing.append(m);seen[m]=dict(module=m,missing=True);return
 r=next(r for r in roots if p.is_relative_to(r));o=r/'.lake/build/lib/lean'/(m.replace('.','/')+'.olean')
 seen[m]=dict(module=m,authority='NOT AUTHORIZED',source=str(p),source_sha256=sha(p),object=str(o),object_sha256=sha(o) if o.is_file() else None)
 imports=re.findall(r'^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.]+)',p.read_text(),re.M)
 seen[m]['imports']=imports
 for d in imports:visit(d)
for m in ['Mathlib.MeasureTheory.Measure.ProbabilityMeasure','Mathlib.MeasureTheory.Integral.Bochner.Basic']:visit(m)
print(json.dumps(dict(manifest_sha256=sha(auth_path),mathlib_revision=subprocess.check_output(['git','-C',str(roots[0]),'rev-parse','HEAD'],text=True).strip(),requested=list(seen.values()),missing=missing,existing_hash_mismatches=[v for v in seen.values() if v.get('expected') and v['expected']!=v['sha256']],compilers_launched=0),indent=2))
