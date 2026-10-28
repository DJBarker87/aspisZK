from pathlib import Path
s='''import PV_B3P_LayoutOffsets226
import PV_B3P_ByteScalar226V3
namespace PV_B3P_ScalarRegions226
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_LayoutOffsets226
set_option autoImplicit false

theorem recipient_tag (p : reference226.OwnedPublic) :
    reference226.byte_at p 69#usize = .ok (.Ok (if p.withdrawal then 0#u8 else 1#u8)) := by
  cases hw : p.withdrawal <;> simp [reference226.byte_at,hw,lift,bind_tc_ok]
#print axioms recipient_tag

theorem withdrawal_tag (p : reference226.OwnedPublic) :
    reference226.byte_at p (if p.withdrawal then 102#usize else 134#usize) =
    .ok (.Ok (if p.withdrawal then 1#u8 else 0#u8)) := by
  cases hw : p.withdrawal with
  | false =>
    simp [reference226.byte_at,hw,lift,bind_tc_ok,c0,c1,c2,c3,c4,c5,c6,c7,c8,c9]
    intro h
    have hm := Nat.mod_le 134 Usize.size
    omega
  | true =>
    simp [reference226.byte_at,hw,lift,bind_tc_ok,c0,c1,c2,c3,c4,c5,c6,c7,c8,c9]
    intro h
    have hm := Nat.mod_le 102 Usize.size
    omega
#print axioms withdrawal_tag
'''
def conditions(w):
 c=70 if w else 102;ind=107 if w else 135;front=ind+8;n=1427 if w else 1455
 return [f'i ≥ {n}#usize','i = 0#usize','i < 33#usize','i < 65#usize','i < 69#usize',
 'i = 69#usize',f'i < {c}#usize',f'i < {c+32}#usize',f'i = {c+32}#usize',
 f'i < {ind}#usize',f'i < {front}#usize']
s+='''theorem amount (p : reference226.OwnedPublic) (i : Usize) (hw : p.withdrawal = true)
    (lo : 103 ≤ i.val) (hi : i.val < 107) :
    reference226.byte_at p i = reference226.field_byte p.withdrawal_amount
      (Usize.wrapping_sub i 103#usize) := by
'''
cond=conditions(True)[:10]
for j,c in enumerate(cond):s+=f'  have h{j} : '+(c if j==len(cond)-1 else f'¬ ({c})')+' := by scalar_tac\n'
s+='  simp only ['+','.join(['reference226.byte_at','hw','↓reduceIte','lift','bind_tc_ok']+[f'c{i}' for i in range(10)]+[f'h{j}' for j in range(len(cond))])+']\n#print axioms amount\n'
s+='''def indexLane (v : U64) (j : Usize) : U8 :=
  UScalar.cast .U8 (U64.wrapping_shr v
    (U32.wrapping_mul 8#u32 (UScalar.cast .U32 j)))

theorem index (p : reference226.OwnedPublic) (i : Usize)
    (lo : (if p.withdrawal then 107 else 135) ≤ i.val)
    (hi : i.val < (if p.withdrawal then 115 else 143)) :
    reference226.byte_at p i = .ok (.Ok (indexLane p.next_pair_index
      (Usize.wrapping_sub i (if p.withdrawal then 107#usize else 135#usize)))) := by
  cases hw : p.withdrawal with
'''
for w in [False,True]:
 s+='  | '+str(w).lower()+' =>\n    simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢\n'
 cond=conditions(w)
 for j,c in enumerate(cond):s+=f'    have h{j} : '+(c if j==len(cond)-1 else f'¬ ({c})')+' := by scalar_tac\n'
 s+='    simp only ['+','.join(['reference226.byte_at','hw','Bool.false_eq_true','↓reduceIte','lift','bind_tc_ok','indexLane']+[f'c{i}' for i in range(10)]+[f'h{j}' for j in range(len(cond))])+']\n'
s+='''#print axioms index

theorem padding (p : reference226.OwnedPublic) (i : Usize)
    (lo : (if p.withdrawal then 1427 else 1455) ≤ i.val) :
    reference226.byte_at p i = .ok (.Ok 0#u8) := by
  cases hw : p.withdrawal with
  | false =>
    simp only [hw,Bool.false_eq_true,↓reduceIte] at lo
    have hn : i ≥ 1455#usize := by scalar_tac
    simp only [reference226.byte_at,hw,Bool.false_eq_true,↓reduceIte,hn,lift,bind_tc_ok]
  | true =>
    simp only [hw,↓reduceIte] at lo
    have hn : i ≥ 1427#usize := by scalar_tac
    simp only [reference226.byte_at,hw,↓reduceIte,hn,lift,bind_tc_ok]
#print axioms padding
end PV_B3P_ScalarRegions226
'''
Path('evidence/pv-b3p6-20261028/lean/PV_B3P_ScalarRegions226.lean').write_text(s)
