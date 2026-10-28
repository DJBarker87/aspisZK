"""Branch-local serializer region equations; no recurrence unfolding."""
from pathlib import Path
D=Path('evidence/pv-b3p6-20261028/lean')
header='''import PV_B3P_LayoutOffsets226
import PV_B3P_DigestValue226V3
import PV_B3P_FrontierOutcome226V3
namespace PV_B3P_LateRegions226
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_LayoutOffsets226
set_option autoImplicit false
'''
s=header
# steps before each returned region, encoded in exactly the source order.
def conditions(w):
 c=70 if w else 102;ind=107 if w else 135;front=ind+8;n=1427 if w else 1455
 return [(f'i ≥ {n}#usize',False),(f'i = 0#usize',False),
 (f'i < 33#usize',False),(f'i < 65#usize',False),(f'i < 69#usize',False),
 (f'i = 69#usize',False),(f'i < {c}#usize',False),(f'i < {c+32}#usize',False),
 (f'i = {c+32}#usize',False),(f'i < {ind}#usize',False),(f'i < {front}#usize',False),
 (f'i < {front+640}#usize',False),(f'i < {front+672}#usize',False)]
specs=[('recipient',70,102,'PV_B3P_DigestTotal226V3.digestAt p.recipient (Usize.wrapping_sub i 70#usize)',6,[False]),
 ('change','(if p.withdrawal then 70 else 102)','(if p.withdrawal then 102 else 134)',
  'PV_B3P_DigestTotal226V3.digestAt p.change (Usize.wrapping_sub i (if p.withdrawal then 70#usize else 102#usize))',7,[False,True]),
 ('frontier','(if p.withdrawal then 115 else 143)','(if p.withdrawal then 755 else 783)',
  'PV_B3P_FrontierOutcome226V3.frontierAt p.frontier (Usize.wrapping_sub i (if p.withdrawal then 115#usize else 143#usize))',11,[False,True]),
 ('next_root','(if p.withdrawal then 755 else 783)','(if p.withdrawal then 787 else 815)',
  'PV_B3P_DigestTotal226V3.digestAt p.next_root (Usize.wrapping_sub (Usize.wrapping_sub i (if p.withdrawal then 115#usize else 143#usize)) 640#usize)',12,[False,True]),
 ('next_frontier','(if p.withdrawal then 787 else 815)','(if p.withdrawal then 1427 else 1455)',
  'PV_B3P_FrontierOutcome226V3.frontierAt p.next_frontier (Usize.wrapping_sub (Usize.wrapping_sub i (if p.withdrawal then 115#usize else 143#usize)) 672#usize)',13,[False,True])]
for name,lo,hi,rhs,last,variants in specs:
 s+=f'theorem {name} (p : reference226.OwnedPublic) (i : Usize)\n'
 if name=='recipient':s+='    (hw : p.withdrawal = false)\n'
 s+=f'    (lo : {lo} ≤ i.val) (hi : i.val < {hi}) :\n    reference226.byte_at p i = {rhs} := by\n'
 if len(variants)>1:
  s+='  cases hw : p.withdrawal with\n'
 for w in variants:
  indent='  '
  if len(variants)>1:
   s+='  | '+('true' if w else 'false')+' =>\n';indent='    '
   s+=indent+'simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢\n'
  cond=conditions(w)
  if last<len(cond):cond=cond[:last+1];cond[-1]=(cond[-1][0],True)
  for j,(c,positive) in enumerate(cond):
   s+=indent+f'have h{j} : '+(c if positive else f'¬ ({c})')+' := by scalar_tac\n'
  facts=['reference226.byte_at','hw','Bool.false_eq_true','↓reduceIte','lift','bind_tc_ok']+[f'c{i}' for i in range(10)]+[f'h{j}' for j in range(len(cond))]+['PV_B3P_DigestTotal226V3.digestAt','PV_B3P_FrontierOutcome226V3.frontierAt']
  s+=indent+'simp only ['+','.join(facts)+']\n'
 s+=f'#print axioms {name}\n'
s+='end PV_B3P_LateRegions226\n';(D/'PV_B3P_LateRegions226.lean').write_text(s)
