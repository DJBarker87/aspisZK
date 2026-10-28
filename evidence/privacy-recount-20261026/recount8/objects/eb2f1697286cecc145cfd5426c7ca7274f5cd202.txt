import R1Z.PV_RunJoin_CoefficientRow44
import R1Z.ProverCommitArray49
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CoefficientArray44
open Aeneas Aeneas.Std Result ProverRwSuccessCoefficientsSource

theorem complete {T : Type} (copy : core.marker.Copy T) (v : transport.Variant) (xs : Nat → T) :
    transport.Variant.coefficients copy v (ProverCommitArray49.array 1024#usize xs) =
      .ok (ProverCommitArray49.array 1024#usize (fun j => xs (AspisR1.rowNat j))) := by
  let rows := ProverCommitArray49.array 1024#usize xs
  let f := transport.Variant.coefficients.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT copy
  have calls : ∀ i : Usize, i.val < (1024#usize).val →
      f.call_mut (rows,v) i = .ok (xs (AspisR1.rowNat i.val),(rows,v)) := by
    intro i hi
    change (do
      let r ← transport.Variant.row v i
      let value ← Array.index_usize rows r
      .ok (value,(rows,v))) = _
    rw [PV_RunJoin_CoefficientRow44.row v i]
    simp only [bind_tc_ok]
    rw [ProverCommitArray49.index 1024#usize xs _ (by
      rw [PV_RunJoin_CoefficientRowMath44.value];exact AspisR1.rowNat_lt i.val)]
    simp only [bind_tc_ok,PV_RunJoin_CoefficientRowMath44.value]
  obtain ⟨a,ha,hav⟩ := ProverRwSuccessArrayFromFn.fromFn_pure 1024#usize f
    (fun i => xs (AspisR1.rowNat i.val)) (rows,v) calls
  have same : a = ProverCommitArray49.array 1024#usize (fun j => xs (AspisR1.rowNat j)) := by
    apply Subtype.ext
    rw [hav]
    simp only [ProverRwSuccessArrayFromFn.indices,List.map_ofFn,ProverCommitArray49.array,Function.comp_def,UScalar.ofNatCore_val_eq,Usize.ofNatCore_val_eq,Fin.val_cast]
  change ProverRwSuccessArrayFromFn.fromFn 1024#usize f (rows,v) = _
  rw [ha,same]
#print axioms complete
end R1Z.PV_RunJoin_CoefficientArray44
