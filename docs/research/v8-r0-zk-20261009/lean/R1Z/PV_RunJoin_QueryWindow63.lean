import R1Z.PV_RunJoin_SliceBound62
import R1Z.PV_RunJoin_SamplerByteIndices54
import R1Z.PV_RunJoin_EncodedInstalled48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryWindow63
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
open PV_RunJoin_WeightInstalled46
abbrev W := aspis_core.field.wide_exact.WideExact

theorem mul4 (q : Usize) (bound : q.val<65536) :
    (Usize.wrapping_mul 4#usize q).val=4*q.val := by
  rw [Usize.wrapping_mul_val_eq]
  change (4*q.val)%UScalar.size .Usize=4*q.val
  exact Nat.mod_eq_of_lt (by have h := PV_RunJoin_SamplerByteIndices54.size;omega)

theorem add4 (q : Usize) (bound : q.val<262144) :
    (Usize.wrapping_add q 4#usize).val=q.val+4 := by
  rw [Usize.wrapping_add_val_eq]
  change (q.val+4)%UScalar.size .Usize=q.val+4
  exact Nat.mod_eq_of_lt (by have h := PV_RunJoin_SamplerByteIndices54.size;omega)

theorem range {T : Type} (xs : Slice T) (first last : Usize) :
    Post (fun s => s.length=last.val-first.val)
      (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice T)
        xs ⟨first,last⟩) := by
  simp only [core.slice.index.Slice.index,core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index]
  split
  · rename_i h
    change (List.slice first.val last.val xs.val).length=last.val-first.val
    simp only [List.slice,List.length_take,List.length_drop]
    have hl : xs.length=xs.val.length := rfl
    rw [hl] at h
    omega
  · trivial

def window (folded : Slice W) (q : Usize) : Result (Slice W) := do
  let quarter ← q / 4#usize
  let first := Usize.wrapping_mul 4#usize quarter
  let last := Usize.wrapping_add first 4#usize
  core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice W) folded ⟨first,last⟩

theorem length (folded : Slice W) (q : Usize) (bound : q.val<262144) :
    Post (fun s => s.length=4) (window folded q) := by
  obtain ⟨quarter,hquarter,hval⟩ := UScalar.div_spec q (y:=4#usize) (by decide)
  have hv : quarter.val=q.val/4 := hval
  have hq : quarter.val<65536 := by omega
  have hm := mul4 quarter hq
  have ha := add4 (Usize.wrapping_mul 4#usize quarter) (by rw [hm];omega)
  simp only [window,hquarter,bind_tc_ok]
  have hr := range folded (Usize.wrapping_mul 4#usize quarter)
    (Usize.wrapping_add (Usize.wrapping_mul 4#usize quarter) 4#usize)
  simpa only [ha,hm,Nat.add_sub_cancel_left] using hr

#print axioms mul4
#print axioms add4
#print axioms range
#print axioms window
#print axioms length
end R1Z.PV_RunJoin_QueryWindow63
