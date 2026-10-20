#!/usr/bin/env python3
"""Adapt only inventoried std externals and the pinned Lean-port shift type."""
import hashlib,json,pathlib,re
HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parents[3]
raw=pathlib.Path('/tmp/cx-ref6-admission-included.lean').read_text()
s=raw.replace('import Aeneas\n','import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\nimport Aeneas.Data.Discriminant\nimport R1Z.BuilderAdmissionStd\n')
changes=[]
patterns=[('core.result.Result.map_err',r'axiom core\.result\.Result\.map_err\n.*?core\.result\.Result T E → O → Result \(core\.result\.Result T F\)',
'''def core.result.Result.map_err
  {T E F O : Type} (f : core.ops.function.FnOnce O E F) :
  core.result.Result T E → O → Result (core.result.Result T F) :=
  R1Z.BuilderAdmissionStd.mapErr f''')]
for method in ['all','any']:
 name='core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.'+method
 patterns.append((name,r'axiom '+re.escape(name)+r'\n.*?core\.slice\.iter\.Iter T → F → Result \(Bool × \(core\.slice\.iter\.Iter T\)\)',
 f'''def {name}
  {{T F : Type}} (f : core.ops.function.FnMut F T Bool) :
  core.slice.iter.Iter T → F → Result (Bool × core.slice.iter.Iter T) :=
  R1Z.BuilderAdmissionStd.{method} f'''))
for name,pat,new in patterns:
 s,n=re.subn(pat,new,s,flags=re.S);assert n==1,(name,n);changes.append(name)
assert s.count('20#i32')==1
s=s.replace('20#i32','20#u32')
assert not re.search(r'\b(axiom|sorry|admit|native_decide)\b',s)
s+='\n#print axioms AspisBuilderAdmissionSource.pool_v1.pair_trace.validate_common\n'
out=ROOT/'docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderAdmissionExtracted.lean'
out.write_text(s)
(HERE/'builder-cont6-admission-adaptation.json').write_text(json.dumps(dict(raw_sha256=hashlib.sha256(raw.encode()).hexdigest(),adapted_sha256=hashlib.sha256(s.encode()).hexdigest(),output=str(out.relative_to(ROOT)),std_definitions=changes,other_changes=['Import env-J Aeneas.Std/RustAttributes and the explicit std models','Literal shift-count type 20i32 to backend-required 20u32; same count','One definition axiom audit'],no_body_or_control_flow_edits=True),indent=2)+'\n')
print(out)
