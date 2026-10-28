"""Compose region branch equations with checked digest/frontier value laws."""
from pathlib import Path
s='''import PV_B3P_LateRegions226
import PV_B3P_FrontierValue226
import PV_B3P_NestedOffset226V3
namespace PV_B3P_LateValue226
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_ByteLayout226V3
set_option autoImplicit false
'''
specs=[('recipient','70','102','p.recipient.val','70#usize','PV_B3P_DigestValue226V3.complete_result',False),
 ('change','(if p.withdrawal then 70 else 102)','(if p.withdrawal then 102 else 134)','p.change.val','(if p.withdrawal then 70#usize else 102#usize)','PV_B3P_DigestValue226V3.complete_result',None),
 ('frontier','(if p.withdrawal then 115 else 143)','(if p.withdrawal then 755 else 783)','PV_B3P_ByteLayout226V3.frontier p.frontier','(if p.withdrawal then 115#usize else 143#usize)','PV_B3P_FrontierValue226.complete_result',None),
 ('next_root','(if p.withdrawal then 755 else 783)','(if p.withdrawal then 787 else 815)','p.next_root.val','(if p.withdrawal then 115#usize else 143#usize)','PV_B3P_DigestValue226V3.complete_result',640),
 ('next_frontier','(if p.withdrawal then 787 else 815)','(if p.withdrawal then 1427 else 1455)','PV_B3P_ByteLayout226V3.frontier p.next_frontier','(if p.withdrawal then 115#usize else 143#usize)','PV_B3P_FrontierValue226.complete_result',672)]
for name,lo,hi,field,start,law,extra in specs:
 offset=f'Usize.wrapping_sub i {start}'
 if type(extra)==int:offset=f'Usize.wrapping_sub ({offset}) {extra}#usize'
 s+=f'theorem {name} (p : reference226.OwnedPublic) (i : Usize)\n'
 if name=='recipient':s+='    (hw : p.withdrawal = false)\n'
 s+=f'''    (lo : {lo} ≤ i.val) (hi : i.val < {hi}) :
    reference226.byte_at p i =
      if ({field})[(i.val-{lo})/4]?.getD 0#u32 < 2147483647#u32 then
        .ok (.Ok ((fields ({field}))[i.val-{lo}]?.getD 0#u8))
      else .ok (.Err aspis_core.state_only_prefix.r0.Error.Public) := by
'''
 offnat=f'i.val-{lo}'
 s+=f'  have hoff : ({offset}).val = {offnat} := by\n'
 if name!='recipient':s+='    cases hw : p.withdrawal <;> simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢\n    all_goals\n      '
 else:s+='    '
 s+='repeat first\n'
 indent='      ' if name!='recipient' else '    '
 s+=indent+'  | rw [PV_B3P_NestedOffset226V3.sub_sub_value _ _ _ (by scalar_tac)]\n'+indent+'  | rw [PV_B3P_Offset226V3.sub_value _ _ (by scalar_tac)]\n'+indent+'scalar_tac\n'
 s+=f'  rw [PV_B3P_LateRegions226.{name} p i '+('hw ' if name=='recipient' else '')+'lo hi]\n'
 s+=f'  rw [{law} _ _ (by\n'
 s+='    rw [hoff]\n'
 if name!='recipient':s+='    cases hw : p.withdrawal <;> simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢ <;> scalar_tac)]\n'
 else:s+='    scalar_tac)]\n'
 s+='  simp only [hoff]\n'
 s+=f'#print axioms {name}\n'
s+='end PV_B3P_LateValue226\n'
Path('evidence/pv-b3p6-20261028/lean/PV_B3P_LateValue226.lean').write_text(s)
