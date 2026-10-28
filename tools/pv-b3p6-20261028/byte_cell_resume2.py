"""Join all thirteen already proved serializer regions on successful bytes."""
from pathlib import Path
D=Path('evidence/pv-b3p6-20261028/lean');ns='PV_B3P_ByteCellValue226'
s='''import PV_B3P_LayoutRegions226
import PV_B3P_DigestRegionValue226V3
import PV_B3P_LateValue226
import PV_B3P_ScalarValue226
namespace PV_B3P_ByteCellValue226
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_ByteLayout226V3
set_option autoImplicit false
attribute [local irreducible] layout fields frontier indexBytes
set_option backward.isDefEq.respectTransparency false in
theorem success_value (p : reference226.OwnedPublic) (i : Usize) (b : U8)
    (h : reference226.byte_at p i = .ok (.Ok b)) (hi : i.val < (layout p).length) :
    b = (layout p)[i.val]?.getD 0#u8 := by
  have hlen := layout_length p
  cases hw : p.withdrawal with
'''
for w in [False,True]:
 name='true' if w else 'false';s+=f'  | {name} =>\n    simp only [hw,Bool.false_eq_true,↓reduceIte] at hlen\n    rw [hlen] at hi\n'
 segs=[('variant',0,1),('anchor',1,33),('nullifier',33,65),('asset',65,69),('recipient_flag',69,70)]
 if not w:segs += [('recipient',70,102)]
 segs += [('change',70 if w else 102,102 if w else 134),('withdrawal_flag',102 if w else 134,103 if w else 135)]
 if w:segs += [('amount',103,107)]
 segs += [('index',107 if w else 135,115 if w else 143),('frontier',115 if w else 143,755 if w else 783),('next_root',755 if w else 783,787 if w else 815),('next_frontier',787 if w else 815,1427 if w else 1455)]
 for ix,(reg,lo,up) in enumerate(segs):
  last=ix==len(segs)-1
  indent='    '
  if not last:s+=f'    by_cases hb{ix} : i.val < {up}\n    ·\n';indent='      '
  s+=indent+f'have hlo : {lo} ≤ i.val := by omega\n'+indent+f'have hup : i.val < {up} := by omega\n'
  isvar=reg in ['change','withdrawal_flag','index','frontier','next_root','next_frontier']
  bounds='(by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hlo) (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hup)' if isvar else 'hlo hup'
  extra='hw ' if reg in ['recipient','amount'] else ''
  s+=indent+f'rw [PV_B3P_LayoutRegions226.{reg} p i.val {extra}{bounds}]\n'
  if reg in ['variant','recipient_flag','withdrawal_flag']:
   s+=indent+f'have hiEq : i = {lo}#usize := by apply UScalar.eq_of_val_eq; change i.val = {lo}; omega\n'
   if reg=='variant':s+=indent+'rw [hiEq,PV_B3P_Regions226V3.discriminant] at h\n'
   if reg=='recipient_flag':s+=indent+'rw [hiEq,PV_B3P_ScalarRegions226.recipient_tag] at h\n'
   if reg=='withdrawal_flag':s+=indent+f'have hid : i = (if p.withdrawal then 102#usize else 134#usize) := by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hiEq\n'+indent+'rw [hid,PV_B3P_ScalarRegions226.withdrawal_tag] at h\n'
   s+=indent+'have hv := (core.result.Result.Ok.inj (Result.ok.inj h)).symm\n'+indent+f'have hzero : i.val - {lo} = 0 := by omega\n'+indent+'simpa only [hw,Bool.false_eq_true,↓reduceIte,hzero,Nat.sub_zero,List.getElem?_cons_zero,Option.getD_some] using hv\n'
  else:
   law='PV_B3P_DigestRegionValue226V3' if reg in ['anchor','nullifier'] else ('PV_B3P_ScalarValue226' if reg in ['asset','amount','index'] else 'PV_B3P_LateValue226')
   s+=indent+f'rw [{law}.{reg} p i {extra}{bounds}] at h\n'
   if reg in ['anchor','nullifier']:s+=indent+f'rw [PV_B3P_Offset226V3.sub_value i {lo}#usize (by simpa using hlo)] at h\n'
   if reg=='index':s+=indent+'exact (core.result.Result.Ok.inj (Result.ok.inj h)).symm\n'
   else:s+=indent+'try simp only [hw,Bool.false_eq_true,↓reduceIte] at h ⊢\n'+indent+'split at h <;> cases h <;> rfl\n'
s+='#print axioms success_value\nend '+ns+'\n'
(D/(ns+'.lean')).write_text(s)
