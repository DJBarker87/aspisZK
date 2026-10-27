from pathlib import Path
import re,sys,hashlib,json
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-runjoin17-20261027'
s=(L/'PV_RunJoin_FixtureHashData.lean').read_text()
out='''import R1Z.PV_RunJoin_HashCallback17
import R1Z.PV_RunJoin_LeafLift16
import R1Z.PV_RunJoin_FixtureNullifier
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NullifierData17
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep
'''
for a in [4,5]:
 for b in [0,23]:
  xs=re.search(rf'def s_{a}_{b} .*? := !\[(.*?)\]',s)[1].split(',')
  out+=f'def s{a}_{b} : State := Array.make 16#usize ['+','.join(x.strip()+'#u32' for x in xs)+']\n'
  out+=f'theorem lift{a}_{b} : liftA (K := PV_RunJoin_FixtureRecords.M) s{a}_{b} = PV_RunJoin_FixtureHashModel.s_{a}_{b} := by\n  funext i\n  fin_cases i <;> rfl\n#print axioms lift{a}_{b}\n'
  out+=f'theorem canon{a}_{b} : Canonical s{a}_{b} := by\n  intro i\n  fin_cases i <;> decide\n#print axioms canon{a}_{b}\n'
out+='end R1Z.PV_RunJoin_NullifierData17\n'
p=L/'PV_RunJoin_NullifierData17.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:p.write_text(out)
print('nullifier data checked: four named states, no recurrence reduction')
