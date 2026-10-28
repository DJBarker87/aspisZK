"""Per-kind raw totality: source branches, symbolic field laws and fixed reads."""
from pathlib import Path
import sys
s='''import R1Z.PV_B2_D_RowRange
import R1Z.PV_B2_D_SubValue
import R1Z.PV_B2_D_PowTotal
set_option autoImplicit false
namespace PV_B2_D_RawTotal
open Aeneas Aeneas.Std Result PV_B2_251c1 PV_B2_C_ArrayTotal
'''
for n in [16,28]:
 for op,name,tac in [('/','div','div_spec'),('%','rem','rem_spec')]:
  s+=f'''theorem {name}{n} (x : Usize) : ∃ q, (x {op} {n}#usize : Result Usize) = ok q ∧ q.val = x.val {op} {n} := by
  have hs : (x {op} {n}#usize : Result Usize) ⦃ q => q.val = x.val {op} {n} ⦄ := by
    apply Usize.{tac}
    decide
  exact WP.spec_imp_exists hs
#print axioms {name}{n}
'''
s+='''theorem kind0 (w : host_weights.Weights) (j : Usize) (hj : j.val < (1024#usize).val) :
    Total (host_weights.raw_value w 0#usize j) := by
  obtain ⟨r,hr,hbound⟩ := PV_B2_D_RowRange.source w.variant j hj
  obtain ⟨i,hi,hival⟩ := div16 r
  obtain ⟨d,hd,hdval⟩ := rem16 r
  have hib : i.val < (64#usize).val := by change i.val < 64; omega
  obtain ⟨mask,hm⟩ := read aspis_core.r0.opening.COPY_ACTIVE_ROW_MASKS i hib
  unfold host_weights.raw_value
  simp only [show (0#usize = 0#usize) = True from by decide,if_true,hr,hi,bind_tc_ok,hm,hd,lift]
  split <;> exact ⟨_,rfl⟩

theorem kind4 (w : host_weights.Weights) (j : Usize) :
    Total (host_weights.raw_value w 4#usize j) := by
  unfold host_weights.raw_value
  simp only [show (4#usize = 0#usize) = False from by decide,if_false,if_pos rfl]
  by_cases hj : j < 56#usize
  · rw [if_pos hj]
    obtain ⟨i,hi,hival⟩ := div28 j
    obtain ⟨d,hd,hdval⟩ := rem28 j
    have hib : i.val < (2#usize).val := by change j.val < 56 at hj; change i.val < 2; omega
    obtain ⟨q,hq⟩ := read w.extra i hib
    obtain ⟨out,ho⟩ := PV_B2_D_PowTotal.source q (UScalar.cast .U64 d)
    simp only [hi,hq,hd,lift,bind_tc_ok,ho]
    exact ⟨_,rfl⟩
  · rw [if_neg hj]
    exact ⟨_,rfl⟩
'''
for k in [1,2,3,5,6]:
 idx=f'Usize.wrapping_sub {k}#usize '+('1#usize' if k<4 else '2#usize')
 s+=f'''theorem kind{k} (w : host_weights.Weights) (j : Usize) (hj : j.val < (1024#usize).val) :
    Total (host_weights.raw_value w {k}#usize j) := by
  have hb5 : ({idx}).val < (5#usize).val := by
    rw [PV_B2_D_SubValue.sub_val _ _ (by scalar_tac)]
    scalar_tac
  have ht : Total (do let a ← Array.index_usize w.factors ({idx}); host_weights.tensor_raw a j) :=
    PV_B2_C_ArrayTotal.bind _ _ (read _ _ hb5) (fun a => PV_B2_D_RawHelpersTotal.tensor a j)
  unfold host_weights.raw_value
  simp only [show ({k}#usize = 0#usize) = False from by decide,if_false,
    show ({k}#usize = 4#usize) = False from by decide,
    show ({k}#usize ≥ 1#usize) = True from by decide,if_true,
    show ({k}#usize ≤ 3#usize) = {str(k<=3).lower().capitalize()} from by decide,
    show ({k}#usize < 4#usize) = {str(k<4).lower().capitalize()} from by decide]
'''
 if k<4:
  s+=f'''  apply PV_B2_C_ArrayTotal.bind _ _ (by
    unfold transport.Variant.Insts.CoreCmpPartialEqVariant.eq
    exact ⟨_,rfl⟩)
  intro bit
  cases bit
  · simpa only [Bool.false_eq_true,if_false,bind_tc_ok] using ht
  · simp only [if_true,lift,bind_tc_ok]
    obtain ⟨r,hr,_⟩ := PV_B2_D_RowRange.source w.variant j hj
    have hb3 : ({idx}).val < (3#usize).val := by
      rw [PV_B2_D_SubValue.sub_val _ _ (by scalar_tac)]
      scalar_tac
    apply PV_B2_C_ArrayTotal.bind _ _ ⟨r,hr⟩
    intro row
    exact PV_B2_C_ArrayTotal.bind _ _ (read _ _ hb3) (fun p => PV_B2_D_RawHelpersTotal.point p row)
'''
 else:s+='  exact ht\n'
 s+=f'#print axioms kind{k}\n'
s+='''theorem source (w : host_weights.Weights) (kind j : Usize)
    (hk : kind.val < 7) (hj : j.val < (1024#usize).val) :
    Total (host_weights.raw_value w kind j) := by
  have hc : kind=0#usize ∨ kind=1#usize ∨ kind=2#usize ∨ kind=3#usize ∨
      kind=4#usize ∨ kind=5#usize ∨ kind=6#usize := by scalar_tac
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact kind0 w j hj
  · exact kind1 w j hj
  · exact kind2 w j hj
  · exact kind3 w j hj
  · exact kind4 w j
  · exact kind5 w j hj
  · exact kind6 w j hj
#print axioms kind0
#print axioms kind4
#print axioms source
end PV_B2_D_RawTotal
'''
p=Path('docs/research/v8-r0-zk-20261009/lean/R1Z/PV_B2_D_RawTotal.lean')
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
