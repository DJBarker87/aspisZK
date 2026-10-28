"""Mathematical layout region values, by symbolic list append indexing."""
from pathlib import Path
s='''import PV_B3P_ByteLayout226V3
namespace PV_B3P_LayoutRegions226
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_ByteLayout226V3
set_option autoImplicit false
'''
specs=[('anchor','1','33','fields p.anchor.val',None),
 ('nullifier','33','65','fields p.nullifier.val',None),
 ('asset','65','69','fields [p.asset_id]',None),
 ('recipient','70','102','fields p.recipient.val',False),
 ('change','(if p.withdrawal then 70 else 102)','(if p.withdrawal then 102 else 134)','fields p.change.val',None),
 ('amount','103','107','fields [p.withdrawal_amount]',True),
 ('index','(if p.withdrawal then 107 else 135)','(if p.withdrawal then 115 else 143)','indexBytes p.next_pair_index',None),
 ('frontier','(if p.withdrawal then 115 else 143)','(if p.withdrawal then 755 else 783)','fields (frontier p.frontier)',None),
 ('next_root','(if p.withdrawal then 755 else 783)','(if p.withdrawal then 787 else 815)','fields p.next_root.val',None),
 ('next_frontier','(if p.withdrawal then 787 else 815)','(if p.withdrawal then 1427 else 1455)','fields (frontier p.next_frontier)',None)]
for name,lo,hi,body,w in specs:
 s+=f'theorem {name} (p : reference226.OwnedPublic) (i : Nat)\n'
 if w is not None:s+=f'    (hw : p.withdrawal = {str(w).lower()})\n'
 s+=f'    (lo : {lo} ≤ i) (hi : i < {hi}) :\n    (layout p)[i]? = ({body})[i-{lo}]? := by\n'
 if w is None:s+='  cases hw : p.withdrawal <;>\n    simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢ <;>\n'
 s+='  '+('  ' if w is None else '')+'simp only [layout,hw,Bool.false_eq_true,↓reduceIte,List.append_assoc,List.nil_append,List.append_nil]\n'
 indent='  '
 if w is None:
  s+='  all_goals\n';indent='    '
 s+=indent+'''repeat first
'''+indent+'''  | rw [List.getElem?_append_right (by
'''+indent+'''      simp only [fields_length,Array.length_eq,frontier_length,indexBytes,
'''+indent+'''        List.length_cons,List.length_nil]
'''+indent+'''      scalar_tac)]
'''+indent+'''  | rw [List.getElem?_append_left (by
'''+indent+'''      simp only [fields_length,Array.length_eq,frontier_length,indexBytes,
'''+indent+'''        List.length_cons,List.length_nil]
'''+indent+'''      scalar_tac)]
'''
 s+=indent+'first\n'+indent+'| rfl\n'+indent+'| congr 1 <;> omega\n'
 s+=f'#print axioms {name}\n'
s+='end PV_B3P_LayoutRegions226\n'
Path('evidence/pv-b3p6-20261028/lean/PV_B3P_LayoutRegions226.lean').write_text(s)
