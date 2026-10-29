from pathlib import Path
L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z')
p=L/'PV_RunJoin_R24NatBounds54.lean';s=p.read_text().replace('b.1.2.val*a.1.2.val≤','a.1.2.val*b.1.2.val≤').replace('by simpa only [Nat.mul_comm] using h.1','h.1');p.write_text(s)
for j,proj in enumerate(['1.1','1.2','2.1','2.2']):
 name=f'PV_RunJoin_R24Value{j}_54';s=f'''import R1Z.PV_RunJoin_R24Equation{j}_54
import R1Z.PV_RunJoin_R24PartialValues54
import R1Z.PV_RunJoin_R24NatBounds54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.{name}
open PV_RunJoin_NeutralValue54 PV_RunJoin_NeutralTowerValue54 PV_RunJoin_CircleNeutralShape53
open PV_RunJoin_R24Inputs54 PV_RunJoin_R24PartialValues54

theorem complete (a b : PV_RunJoin_NeutralTowerValue54.Q) (ha : QC a) (hb : QC b) :
    (PV_RunJoin_R24Equation{j}_54.accumulator a b (u a b) (v a b) : M)=
      (qm (qv a) (qv b)).{proj} := by
'''
 if j==0:s+='  have h := PV_RunJoin_R24NatBounds54.first a b ha hb\n  rw [PV_RunJoin_R24Equation0_54.accumulator,Nat.cast_sub h.2]\n  rw [Nat.cast_add,Nat.cast_add,Nat.cast_sub h.1]\n'
 elif j==2:s+='  have h := PV_RunJoin_R24NatBounds54.third a b ha hb\n  rw [PV_RunJoin_R24Equation2_54.accumulator,Nat.cast_sub h.2,Nat.cast_sub h.1]\n'
 else:s+=f'  unfold PV_RunJoin_R24Equation{j}_54.accumulator\n'
 s+='  simp only [Nat.cast_add,Nat.cast_mul]\n'
 if j in (0,1):s+='  rw [u_value a b ha hb,v_value a b]\n'
 if j==0:s+='  rw [square_zero,prime_zero]\n'
 elif j==2:s+='  rw [square_zero]\n'
 s+='  simp only [qm,qv,ca,cs,cm,cr,cv,scalar,Prod.fst,Prod.snd]\n  ring\n#print axioms complete\nend R1Z.'+name+'\n';(L/(name+'.lean')).write_text(s)
