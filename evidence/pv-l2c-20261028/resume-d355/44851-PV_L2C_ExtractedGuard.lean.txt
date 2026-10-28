import PV_L2C_SelectedDense
set_option autoImplicit false
namespace PV_L2C_ExtractedGuard
open Aeneas Aeneas.Std Result AspisR1ProverBalance9
open PV_L2C_NativeQ PV_L2C_PaddingNative PV_L2C_QFold PV_L2C_ReferenceQ
open PV_L2C_VecRead PV_L2C_RowEnumeration PV_L2C_SelectedDense

/-- Complete extracted owned balance result and the two raw table predicates.
The supplied table is the sampler shape on arbitrary canonical random values;
this theorem does not assume either rejection predicate is false. -/
theorem padding_result (active : Fin 1024 → Bool) (d : Fin 1024) (random : Fin 1024 → Q)
    (hc : ∀ i,Canonical (random i)) (hd : active d=false) :
    prover_commit_reference.balance_qm31_owned
      (vector bound1024 (fun i => source (sample active d random i))) (index d)
      (PV_L2C_VecRead.active active)=
        ok (.Ok (),vector bound1024 (fun i => source (rebalance active d (sample active d random) i))) ∧
    (∀ i,(active i && decide (rebalance active d (sample active d random) i≠zero))=false) ∧
    decide (tableSum (inactiveTable active (rebalance active d (sample active d random)))≠zero)=false := by
  have hb : (index d).val<1024 := by rw [index_val];exact d.isLt
  have ha : active ⟨(index d).val,hb⟩=false := by simpa only [index_val] using hd
  refine ⟨?_,guard_outcomes active d random hc hd⟩
  rw [PV_L2C_OwnedBalance.complete_result _ active (index d) hb ha,
    output_eq _ active d (sample_canonical active d random hc)]
#print axioms padding_result
end PV_L2C_ExtractedGuard
