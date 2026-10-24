"""Retain concrete emitted control; turn every external hole into an explicit parameter."""
from pathlib import Path
import re,json,hashlib,sys
D=Path(__file__).resolve().parent;R=D.parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
G=D/'body-generated';N='ProverRwRngNativeBody'
sha=lambda b:hashlib.sha256(b).hexdigest()
def decls(p):
 s=p.read_text();return [(m[1],m[2].strip()) for m in re.finditer(r'\baxiom\s+([\w.]+)([\s\S]*?)(?=\n/--|\Z)',s)]
pre='import Aeneas\nopen Aeneas Aeneas.Std Result ControlFlow\nnoncomputable section\nnamespace '+N+'\n'
ts=decls(G/'TypesExternal_Template.lean');ty=pre+'class TypeLeaves where\n'
for i,(n,tail) in enumerate(ts):ty+=f'  t{i} {tail}\n'
ty+='variable [TypeLeaves]\n'
for i,(n,tail) in enumerate(ts):ty+=f'abbrev {n} := @TypeLeaves.t{i} _\n'
t=(G/'Types.lean').read_text().split('namespace '+N+'\n',1)[1].rsplit('end '+N,1)[0]
# Discriminant attributes generate unqualified globals; the ADTs remain unchanged.
t=re.sub(r'@\[discriminant isize,\s*', '@[',t).replace('@[discriminant isize]\n','')
ty+=t+'attribute [discriminant isize] aspis_prover.state_only_hiding.StateOnlyMaskBuildError\nend '+N+'\n'
fs=decls(G/'FunsExternal_Template.lean');le='import R1Z.ProverRwRngNativeBodyTypes\n'+pre.split('\n',1)[1]+'variable [TypeLeaves]\n'
# Same source-shaped map_err installation as accepted predecessor; no external hypothesis.
le+='''def core.result.Result.map_err {T E F O : Type}
    (inst : core.ops.function.FnOnce O E F)
    (status : core.result.Result T E) (closure : O) : Result (core.result.Result T F) :=
  match status with
  | .Ok x => .ok (.Ok x)
  | .Err e => do
    let mapped ← inst.call_once closure e
    .ok (.Err mapped)
'''
fs=[x for x in fs if x[0]!='core.result.Result.map_err']
le+='class LocalLeaves where\n'
for i,(n,tail) in enumerate(fs):le+=f'  f{i} {tail}\n'
le+='variable [LocalLeaves]\n'
for i,(n,tail) in enumerate(fs):le+=f'def {n} := @LocalLeaves.f{i} _ _\n'
le+='end '+N+'\n'
f=(G/'Funs.lean').read_text().split('namespace '+N+'\n',1)[1]
f=f.replace('impl_def aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31','def aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31').replace('core.cmp.PartialEq.ne.trait_default\n    aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31','core.cmp.PartialEq.ne.default\n    aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq')
em='import R1Z.ProverRwRngNativeBodyLeaves\n'+pre.split('\n',1)[1]+'variable [TypeLeaves] [LocalLeaves]\n'+f
outputs={'ProverRwRngNativeBodyTypes.lean':ty,'ProverRwRngNativeBodyLeaves.lean':le,'ProverRwRngNativeBodyEmission.lean':em}
for n,s in outputs.items():
 if '--check' in sys.argv:assert (L/n).read_text()==s
 else:(L/n).write_text(s)
record=dict(raw={p.name:sha(p.read_bytes()) for p in G.iterdir() if p.is_file()},outputs={n:sha(s.encode()) for n,s in outputs.items()},type_parameters=[dict(field='t'+str(i),qualified=n,signature=s) for i,(n,s) in enumerate(ts)],local_leaves=[dict(field='f'+str(i),qualified=n,signature=s) for i,(n,s) in enumerate(fs)],changes=['external type holes become explicit TypeLeaves fields, never installed native sorts','external function holes become explicit LocalLeaves fields, no whole-execution equality field','source-shaped Result.map_err branch installation reused','remove generated resource overrides; retain discriminant attribute only for the concrete mask-error equality consumer; other unused attributes removed to avoid global collisions','expand QM31 trait-default impl_def to its equivalent nonrecursive def using PartialEq.ne.default eq (raw macro failed kernel free-variable check); no source operation/control or backend change'],physical_zeroize='Explicit LocalLeaves field, no value-level zeroization or physical destruction claim',native_body='actual borrowed-store call emission returns (Result,Store); no FnMut body/owned-store substitution; native audit retained')
p=D/'body-adaptation.json';s=json.dumps(record,indent=2)+'\n'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
print('adapted',len(ts),'type parameters and',len(fs),'explicit local leaves')
