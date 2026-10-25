#!/usr/bin/env python3
"""Read-only reassessment of inherited source evidence; no extraction/build."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2]
E=R/'evidence/port25array-20261024'
old=R/'evidence/port23push-20261024'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# Execute unchanged checks with only the evidence output destination redirected.
script=R/'tools/port23push-20261024/Port23PUSH_audit.py'
s=script.read_text().replace("E=R/'evidence/port23push-20261024'", "E=R/'evidence/port25array-20261024'")
# Inputs remain pinned inherited artifacts; never copy or reinterpret the template.
s=s.replace("j=json.loads((E/'Port23PUSH.llbc')", "j=json.loads((old/'Port23PUSH.llbc')")
s=s.replace("pins=json.loads((E/'source-pins.json')", "pins=json.loads((old/'source-pins.json')")
s=s.replace("p=E/'Port23PUSH-generated'/name", "p=old/'Port23PUSH-generated'/name")
s=s.replace("script_sha256=sha(pathlib.Path(__file__).read_bytes())", "script_sha256=sha(script.read_bytes())")
exec(compile(s,str(script),'exec'),dict(__file__=str(script),old=old,script=script))
graph=json.loads((old/'std-source-graph-focused.json').read_text())
selected=[]
for f in graph['files']:
 if any(x in f['path'] for x in ['core/src/array/mod.rs','core/src/slice/mod.rs','core/src/slice/iter.rs']):
  hits=[h for h in f['hits'] if h['needle'] in ['fn into_iter(self) -> IterMut','pub const fn iter_mut(',"pub(super) const fn new(slice: &'a mut [T])"]]
  selected.append(dict(path=f['path'],whole_sha256=f['sha256'],bytes=f['bytes'],hits=hits))
checks={}
for run in ['lean-001','lean-003','lean-007']:
 p=E/run/'command.json'
 if p.exists():
  c=json.loads(p.read_text())
  checks[run]=dict(source_sha256=c['source_sha256'],dependencies=c['dependencies'],
    source_revision=c['source_revision'])
out=dict(schema='Port25ARRAY-source-assessment-v1',
 command='python3 tools/port25array-20261024/Port25ARRAY_sourceaudit.py',
 script_sha256=sha(Path(__file__)),revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True,cwd=R).strip(),
 inherited_graph=dict(path=str((old/'std-source-graph-focused.json').relative_to(R)),sha256=sha(old/'std-source-graph-focused.json'),new_native_identity_gate=False),
 literal_delegation=selected,
 assessed_inputs={str(p.relative_to(R)):dict(sha256=sha(p),bytes=p.stat().st_size) for p in [old/'Port23PUSH.llbc',old/'source-pins.json',old/'Port23PUSH-generated/Funs.lean.txt',old/'Port23PUSH-generated/FunsExternal_Template.lean.txt',R/'docs/research/100bit-spend-path-20261013/lean/Port23PUSH_Source.lean']},
 focused_checks=checks,
 established='existing content wrapper composition and scalar facts only; inspect Lean receipts for accepted declarations',
 retained=['raw generated template/caller ABI mismatch','native/compiler association of new composition to missing external is not installed','actual complete mutable row equivalence','fixed native primitive effects and ordered rejected prefix','full op6 and trace/observer composition'],
 trust='no fields or assumptions added; D157 existing pure content interpretation only, no unsafe/panic/allocator policy expansion',
 early_integrity='Port23 lean-001..004 lack explicit post/sysroot snapshots; no retroactive repair claimed')
(E/'source-assessment.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(literal_delegation=selected,old_template_unchanged=True,new_native_association=False)))
