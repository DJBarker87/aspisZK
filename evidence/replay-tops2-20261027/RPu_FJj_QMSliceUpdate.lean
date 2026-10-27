import RPu_FJj_QMSlice
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_QMSliceUpdate
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NQ qm)

theorem value (s out : Slice NQ) (i : Usize) (x : NQ) (j : Nat)
    (run : Slice.update s i x=ok out) :
    FJj_QMSlice.value out j=if i.val=j then decodeQM (qm x) else FJj_QMSlice.value s j := by
  unfold Slice.update at run
  split at run
  · cases run
  · rename_i h
    cases Result.ok.inj run
    have hi : i.val < s.val.length := by
      change s.val[i.val]?=some _ at h
      exact (List.getElem_of_getElem? h).choose
    simp only [FJj_QMSlice.value,List.getElem?_set]
    by_cases eq : i.val=j
    · have hj : j < s.val.length := eq ▸ hi
      simp only [eq,if_pos hj,if_true]
    · simp only [eq,if_false]

theorem length (s out : Slice NQ) (i : Usize) (x : NQ)
    (run : Slice.update s i x=ok out) : out.val.length=s.val.length := by
  rw [FJj_QMSlice.update s out i x run,List.length_set]
#print axioms value
#print axioms length
end AspisR1.FJj_QMSliceUpdate
end
