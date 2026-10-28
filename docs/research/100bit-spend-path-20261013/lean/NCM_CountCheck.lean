import NCM_CountCarrier

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_CountCheck
open Aeneas Aeneas.Std NCE_OpeningCuts NCE_CountCuts NCE_CountInitCuts
open NCE_CountRowCuts NCE_CountLevelCuts MultiproofConePhysicalViews MultiproofConeCountPhysical
attribute [local instance] Classical.propDecidable

/-- All count outcomes, including malformed/empty admission. The only native
facts are five count steps and the one-window admission predicates. -/
theorem association (ops : NCM_CountCarrier.Ops)
    (zero : NCE_Native_CountZero ops.create) (copy : NCE_Native_CountCopy ops.copy)
    (scan : NCE_Native_CountScan ops.scan) (store : NCE_Native_CountCommit ops.store)
    (height : NCE_Native_CountHeight ops.height)
    (pair range : NCE_AdmissionCuts.Predicate) (predicates : NCE_AdmissionCuts.NCE_Native_Admission pair range)
    (s : Carrier) :
    NCM_CountCarrier.count ops pair range s =
      if OraclePortFrozenOrder.wellFormed ((live s.scratch 0 s.scratch.n.val).map Prod.fst) then
        some (MultiproofConeSlotTail.slotCount s.scratch,s) else none := by
  have keys := NCE_VerifierAdmission.same_indices s
  have length : ((live s.scratch 0 s.scratch.n.val).map Prod.fst).length = s.scratch.n.val := by
    simp only [List.length_map,MultiproofConeRootGuard.live_length]
  by_cases big : 16 < s.scratch.n.val
  · have invalid : ¬OraclePortFrozenOrder.wellFormed ((live s.scratch 0 s.scratch.n.val).map Prod.fst) := by
      intro valid
      have size := valid.2.1
      omega
    simp only [NCM_CountCarrier.count,big,if_true,invalid,if_false]
  · have small : s.scratch.n.val ≤ 16 := by omega
    rw [NCM_CountCarrier.count,if_neg big,NCE_AdmissionCuts.check_eq pair range predicates s small]
    simp only
    cases admitted : NBI_Admission.admission (cells (NCE_AdmissionCuts.index s) 0 s.scratch.n.val) with
    | false =>
      have invalid : ¬OraclePortFrozenOrder.wellFormed ((live s.scratch 0 s.scratch.n.val).map Prod.fst) := by
        intro valid
        have wf : OraclePortFrozenOrder.wellFormed (cells (NCE_AdmissionCuts.index s) 0 s.scratch.n.val) := by rw [keys];exact valid
        have yes := (NBI_Admission.admission_iff _).mpr wf
        rw [admitted] at yes
        cases yes
      simp only [Bool.false_eq_true,if_false,invalid]
    | true =>
      have well : OraclePortFrozenOrder.wellFormed ((live s.scratch 0 s.scratch.n.val).map Prod.fst) := by
        rw [←keys]
        exact (NBI_Admission.admission_iff _).mp admitted
      simp only [if_true,well,NCM_CountCarrier.valid ops zero copy scan store height s well]

#print axioms association
end AspisR1.NCM_CountCheck
end
