"""Read-only namespace-root resolution audit after attempt 71000. No compiler calls."""
from pathlib import Path
import json,hashlib
B=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
roots=[B/'objects',B.parent/'codex-cx-reconcile-cache-20261028/objects',Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')]
manifest=json.load(open(B/'NDR_FINAL_COHORT_PINS.json'));missing=[];shadowed=[]
for v in manifest['entries']:
 m=v['module'];pkg=m.split('.')[0]
 root=next(r for r in roots if (r/pkg).is_dir() or (r/(pkg+'.olean')).exists())
 p=root/(m.replace('.','/')+'.olean')
 if not p.exists():missing.append(dict(module=m,selected_path=str(p),authoritative_path=v['object_path'],expected_sha256=v['object_sha256']))
 elif str(p)!=v['object_path']:shadowed.append(dict(module=m,selected_path=str(p),authoritative_path=v['object_path'],selected_sha256=sha(p),expected_sha256=v['object_sha256']))
source=Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/src/lean/Lean/Util/Path.lean')
lines=source.read_text().splitlines()
q=roots[1]/'Mathlib/Data/Real/Basic.olean'
result=dict(status='STOPPED; first module failed before elaboration; no retry',attempt=71000,failure_class='pre-elaboration environment: Lean package root shadowing',exact_error=(B/'lean-71000/stdout.log').read_text(),LEAN_PATH=':'.join(map(str,roots)),resolution_source=dict(path=str(source),sha256=sha(source),excerpt='\n'.join(f'{i+1}: {lines[i]}' for i in list(range(55,72))+list(range(115,125)))),witness=dict(module='Mathlib.Data.Real.Basic',authoritative_path=str(q),authoritative_sha256=sha(q),selected_path=str(roots[0]/'Mathlib/Data/Real/Basic.olean'),selected_exists=False,new_mathlib_root_exists=(roots[0]/'Mathlib').is_dir()),missing_effective_ndr_modules=missing,shadowed_ndr_modules=shadowed,repair_proposed_only='Materialize complete read-only NDR namespace overlays in the new directory, with private per-file links/copies to authoritative NDR objects and companions and private slots for reconciliation outputs; never compile through a symlink into NDR. Then verify Lean package-root resolution for the whole closure. No repair or retry is performed in this task.',source_revision='2e3a5fe870',consumer_sha256=json.load(open(B/'plan.json'))['consumer_sha256'])
(B/'isolation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(status=result['status'],missing_effective_ndr_modules=len(missing),shadowed_ndr_modules=len(shadowed),witness=result['witness'])))
