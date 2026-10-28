from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin31-20261028';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';G=E/'pv31-lane-reference-aeneas-06-generated'
(L/'PV_RunJoin_LaneTypesExternal31.lean').write_text('''import R1Z.PV_RunJoin_OuterTypes30
set_option autoImplicit false
namespace PV_RunJoin_Lane31
abbrev aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError :=
  R1Z.BuilderForestAdmissionPort.pool_v1.incremental_merkle.PoolV1TreeError
abbrev aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError :=
  PV_RunJoin_Outer30.pool_v1.payment_relation.PV30_PoolV1PaymentStatementFormatError
end PV_RunJoin_Lane31
''')
for kind in ['Types','Funs']:
 s=(G/(kind+'.lean')).read_text().replace('import Pv31-lane-reference-names-03.TypesExternal','import R1Z.PV_RunJoin_LaneTypesExternal31').replace('import Pv31-lane-reference-names-03.Types','import R1Z.PV_RunJoin_LaneTypes31').replace('import Pv31-lane-reference-names-03.FunsExternal','import R1Z.PV_RunJoin_LaneExternal31')
 if kind=='Funs':s=s.replace('namespace PV_RunJoin_Lane31','namespace PV_RunJoin_Lane31\nvariable [R1Z.BuilderForestAdmissionPort.ExternalLinear]')
 (L/('PV_RunJoin_Lane'+kind+'31.lean')).write_text(s)
leaf='aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1'
err='aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLeafErrorV1'
s='''import R1Z.PV_RunJoin_LaneTypes31
import R1Z.BuilderAdmissionStd
set_option autoImplicit false
noncomputable section
namespace PV_RunJoin_Lane31
open Aeneas Aeneas.Std Result
abbrev core.result.Result.map_err := @R1Z.BuilderAdmissionStd.mapErr
'''
s+=f'''def leafToForest (x : {leaf}) :
    R1Z.BuilderForestAdmissionPort.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1 :=
  ⟨x.first_commitment,x.second_occupied,x.second_commitment,x.second_occupancy_inverse⟩

def leafErrorFromForest : R1Z.BuilderForestAdmissionPort.pool_v1.pair_tree_profile.PoolV1PairLeafErrorV1 → {err}
'''
t=(G/'Types.lean').read_text();a=t.index('inductive '+err);b=t.index('/--',a);names=re.findall(r'^\| (\w+)',t[a:b],re.M)
s+=''.join(f'  | .{n} => .{n}\n' for n in names)
s+='''
variable [R1Z.BuilderForestAdmissionPort.ExternalLinear]
def aspis_statement.pool_v1.format.pool_v1_tree_parent :=
  R1Z.BuilderForestAdmissionPort.pool_v1.format.pool_v1_tree_parent
'''
s+=f'''def {leaf}.leaf_digest (x : {leaf}) :
    Result (core.result.Result (Array U32 8#usize) {err}) := do
  let r ← R1Z.BuilderForestAdmissionPort.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.leaf_digest (leafToForest x)
  ok (match r with | .Ok d => .Ok d | .Err e => .Err (leafErrorFromForest e))
end PV_RunJoin_Lane31
'''
(L/'PV_RunJoin_LaneExternal31.lean').write_text(s)
rows=[]
for kind in ['Types','Funs']:
 p=L/('PV_RunJoin_Lane'+kind+'31.lean');rows.append(dict(path=str(p.relative_to(R)),raw_sha256=hashlib.sha256((G/(kind+'.lean')).read_bytes()).hexdigest(),installed_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),changes='import paths; explicit ExternalLinear dictionary in Funs only'))
(E/'lane-emission-install.json').write_text(json.dumps(rows,indent=2)+'\n')
