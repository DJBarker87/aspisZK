from pathlib import Path
import hashlib,argparse
SN='AspisR1S9SquareMulQMCutV1.field'
TN='AspisR1S9ActualQMMulCutV1.field'
ops=[('mul',['x.c0','y.c0']),('mul',['x.c1','y.c1']),('add',['x.c0','x.c1']),('add',['y.c0','y.c1']),('mul',[2,3]),('byr',[1]),('add',[0,5]),('sub',[4,0]),('sub',[7,1])]
def src_atom(a):return f's{a}' if isinstance(a,int) else a
def tgt_atom(a,env):return env[a] if isinstance(a,int) else f'(mapCM {a})'
def call(i,target=False,env=None):
 op,args=ops[i];ns=TN if target else SN
 fun=f'{ns}.mul_by_r' if op=='byr' else f'{ns}.CM31.{op}'
 atoms=[tgt_atom(a,env) if target else src_atom(a) for a in args]
 return fun+' '+' '.join(atoms)
def body(start,target=False,prior=None,indent='      '):
 env=dict(prior or {});out=[]
 for j in range(start,9):
  var=f't{j}' if target else f's{j}'
  out.append(indent+f'let {var} ← '+call(j,target,env))
  env[j]=var
 vals=[env[j] if target else f's{j}' for j in (6,8)]
 typ='TargetQM' if target else 'SourceQM'
 out.append(indent+f'ok ({{ c0 := {vals[0]}, c1 := {vals[1]} }} : {typ})')
 return '\n'.join(out)
header=f'''import S9QMSquareMixedProductMapV1
import S9QMSquareByRMapV1
import S9SourceResultTransportV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9GeneratedCombinedQMResultV1
abbrev SourceCM := {SN}.CM31
abbrev TargetCM := {TN}.CM31
abbrev SourceQM := {SN}.QM31
abbrev TargetQM := {TN}.QM31
abbrev mapCM : SourceCM → TargetCM := AspisR1S9QMSquareMixedProductMapV1.mapActualCM
def mapQM (q : SourceQM) : TargetQM := ⟨mapCM q.c0,mapCM q.c1⟩
abbrev mapResult {{A B : Type}} (f : A → B) (r : Result A) : Result B :=
  AspisR1S9SourceResultTransportV1.mapResult f r

/-- Exact source call order. Scoped source and target names are distinct.
Every component map preserves failure and divergence; no success is assumed. -/
theorem combined_qm_mul_maps (x y : SourceQM) :
    mapResult mapQM ({SN}.QM31.mul x y) =
      {TN}.QM31.mul (mapQM x) (mapQM y) := by
  unfold {SN}.QM31.mul {TN}.QM31.mul
  change mapResult mapQM (do
{body(0)} ) = (do
{body(0,True)} )
'''
s=header
for i,(op,args) in enumerate(ops):
 prior={j:f'(mapCM s{j})' for j in range(i)}
 targetenv=dict(prior);targetenv[i]=f't{i}'
 h=('AspisR1S9QMSquareByRMapV1.by_r_maps_to_actual' if op=='byr' else f'AspisR1S9QMSquareMixedProductMapV1.cm_{op}_map')+' '+' '.join(src_atom(a) for a in args)
 s+=f'''  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq mapCM mapQM
    ({call(i)})
    ({call(i,True,prior)})
    (fun s{i} => do
{body(i+1,False,indent='      ')})
    (fun t{i} => do
{body(i+1,True,targetenv,indent='      ')})
    ({h})
  intro s{i}
'''
s+='''  rfl
#print axioms combined_qm_mul_maps
end AspisR1S9GeneratedCombinedQMResultV1
'''
a=argparse.ArgumentParser();a.add_argument('--output',default='/tmp/root-s9-generated-combined-qm-result-v1-20261023/sources/S9GeneratedCombinedQMResultV1.lean');a.add_argument('--check',action='store_true');args=a.parse_args();p=Path(args.output)
if args.check: assert p.read_text()==s,'generated source mismatch'
else: p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
print(hashlib.sha256(p.read_bytes()).hexdigest())
