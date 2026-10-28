"""Layout indexing by one generic prefix/body/suffix lemma, never value reduction."""
from pathlib import Path
s='''import PV_B3P_ByteLayout226V3
import PV_B3P_LayoutIndex226
namespace PV_B3P_LayoutRegions226
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_ByteLayout226V3
set_option autoImplicit false
attribute [local irreducible] fields PV_B3P_ByteLayout226V3.frontier indexBytes
'''
def chain(xs):return '[]' if not xs else '('+' ++ '.join('('+x+')' for x in xs)+')'
def schema(w):
 xs=[('variant','[1#u8]' if w else '[0#u8]',1),('anchor','fields p.anchor.val',32),('nullifier','fields p.nullifier.val',32),('asset','fields [p.asset_id]',4),('recipient_flag','[0#u8]' if w else '[1#u8]',1)]
 if not w:xs+=[('recipient','fields p.recipient.val',32)]
 xs += [('change','fields p.change.val',32),('withdrawal_flag','[1#u8]' if w else '[0#u8]',1)]
 if w:xs+=[('amount','fields [p.withdrawal_amount]',4)]
 xs += [('index','indexBytes p.next_pair_index',8),('frontier','fields (PV_B3P_ByteLayout226V3.frontier p.frontier)',640),('next_root','fields p.next_root.val',32),('next_frontier','fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier)',640)]
 return xs
specs=[('variant','0','1','[if p.withdrawal then 1#u8 else 0#u8]',None),('recipient_flag','69','70','[if p.withdrawal then 0#u8 else 1#u8]',None),('withdrawal_flag','(if p.withdrawal then 102 else 134)','(if p.withdrawal then 103 else 135)','[if p.withdrawal then 1#u8 else 0#u8]',None),('anchor','1','33','fields p.anchor.val',None),('nullifier','33','65','fields p.nullifier.val',None),('asset','65','69','fields [p.asset_id]',None),('recipient','70','102','fields p.recipient.val',False),('change','(if p.withdrawal then 70 else 102)','(if p.withdrawal then 102 else 134)','fields p.change.val',None),('amount','103','107','fields [p.withdrawal_amount]',True),('index','(if p.withdrawal then 107 else 135)','(if p.withdrawal then 115 else 143)','indexBytes p.next_pair_index',None),('frontier','(if p.withdrawal then 115 else 143)','(if p.withdrawal then 755 else 783)','fields (PV_B3P_ByteLayout226V3.frontier p.frontier)',None),('next_root','(if p.withdrawal then 755 else 783)','(if p.withdrawal then 787 else 815)','fields p.next_root.val',None),('next_frontier','(if p.withdrawal then 787 else 815)','(if p.withdrawal then 1427 else 1455)','fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier)',None)]
lens='fields_length,Array.length_eq,frontier_length,indexBytes,List.length_append,List.length_cons,List.length_nil,h8'
for name,lo,hi,body,variant in specs:
 s+='set_option backward.isDefEq.respectTransparency false in\n'
 s+=f'theorem {name} (p : reference226.OwnedPublic) (i : Nat)\n'
 if variant is not None:s+=f'    (hw : p.withdrawal = {str(variant).lower()})\n'
 s+=f'    (lo : {lo} ≤ i) (hi : i < {hi}) :\n    (layout p)[i]? = ({body})[i-{lo}]? := by\n'
 s+='  have h8 : (8#usize).val = 8 := rfl\n'
 if variant is None:s+='  cases hw : p.withdrawal with\n'
 for w in ([False,True] if variant is None else [variant]):
  indent='  '
  if variant is None:s+='  | '+str(w).lower()+' =>\n';indent='    '
  s+=indent+'try simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢\n'
  xs=schema(w);k=next(k for k,x in enumerate(xs) if x[0]==name)
  pre=chain([x[1] for x in xs[:k]]);b=xs[k][1];post=chain([x[1] for x in xs[k+1:]]);start=sum(x[2] for x in xs[:k])
  s+=indent+f'have he : layout p = {pre} ++ ({b}) ++ {post} := by\n'+indent+'  simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]\n'
  s+=indent+'rw [he]\n'
  s+=indent+f'apply PV_B3P_LayoutIndex226.at_segment {pre} ({b}) {post} i {start}\n'
  s+=indent+f'· simp only [{lens}]\n'
  s+=indent+'· exact lo\n'
  s+=indent+f'· simp only [{lens}]\n'+indent+'  omega\n'
 s+=f'#print axioms {name}\n'
s+='end PV_B3P_LayoutRegions226\n'
Path('evidence/pv-b3p6-20261028/lean/PV_B3P_LayoutRegions226.lean').write_text(s)
