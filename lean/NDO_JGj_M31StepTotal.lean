import NDO_JGj_M31ScalarTotal
import RPv_FJb_M31Step
import RPv_JFy_ArrayTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_M31StepTotal
open Aeneas Aeneas.Std Result WP FIq_Native
open FIw_ArrayValue (canonical)
open FJb_MatrixGroupStep (State)
open FJb_M31Step (Constants Bounded)
theorem source (s : State) (a : Constants) (i : Usize)
    (hi : i.val<(16#usize).val) (hs : canonical s) (ha : Bounded a) :
    ∃ out,FJb_M31Step.step s a i=ok out ∧ canonical out := by
  obtain ⟨x,rx,cx⟩ := JFy_ArrayTotal.read s i hi hs
  let c := FJb_TailCell.cell a ⟨i.val,hi⟩
  have rc : Array.index_usize a i=ok c := RawPoseidonExternalRowReads.array_index_usize_ok a i hi
  obtain ⟨m,q,rm,rq,cq⟩ := JGj_M31ScalarTotal.source x c cx (ha _)
  have hmut : Array.index_mut_usize s i=ok (x,fun z=>s.set i z) := by
    simp only [Array.index_mut_usize,rx,bind_tc_ok]
  let u := FJb_M31Scalar.updated x m
  let s1 := s.set i u
  have again : Array.index_usize s1 i=ok u := by
    rw [RawPoseidonExternalRowReads.array_index_usize_ok s1 i hi]
    congr 1
    change (s.val.set i.val u)[i.val]'_=u
    exact List.getElem_set_self (by simpa only [List.length_set,s.property] using hi)
  obtain ⟨out,ro,vo⟩ := WP.spec_imp_exists (Array.update_spec s1 i q (by simpa only [s1.property] using hi))
  have overwrite : s1.set i q=s.set i q := by
    apply Subtype.ext
    simp only [s1,Array.set_val_eq,List.set_set]
  have original : Array.update s i q=ok out := by
    obtain ⟨z,rz,vz⟩ := WP.spec_imp_exists (Array.update_spec s i q (by simpa only [s.property] using hi))
    exact rz.trans (congrArg Result.ok (vz.trans (vo.trans overwrite).symm))
  refine ⟨out,?_,(FIw_ArrayValue.update s out i q hi hs cq original).1⟩
  unfold FJb_M31Step.step
  rw [rx,bind_tc_ok,rc,bind_tc_ok,rm,bind_tc_ok,hmut,bind_tc_ok]
  change (do let x2 ← Array.index_usize s1 i;let r ← state_only_poseidon.pow5 x2;Array.update s1 i r)=ok out
  rw [again,bind_tc_ok,rq,bind_tc_ok,ro]
#print axioms source
end AspisR1.JGj_M31StepTotal
end
