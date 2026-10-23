import AspisR1S9ActualWeightsNewBoxNewV3.Funs
import S9ConstructorV3SuccessorCarryLoopCanonicalV1
import S9ConstructorV3StatementCellCanonicalV1
import S9ConstructorV3Loop1CellCanonicalV1
import S9ConstructorV3QMAddSubCanonicalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ConstructorV3StatementProducerCanonicalV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
open AspisR1S9ConstructorV3SuccessorCarryBodyCanonicalV1
open AspisR1S9ConstructorV3StatementCellCanonicalV1
open AspisR1S9ActualWeightsNewBoxNewV3

theorem vector_update_canonical (a out : Vector) (i : Usize) (x : Q)
    (ha : VectorCanonical a) (hx : CanQ (toProbeQ x))
    (hupdate : Array.update a i x = .ok out) : VectorCanonical out := by
  exact AspisR1S9PairArrayUpdateCanonicalV1.update_preserves_canonical_reads
    toProbeQ CanQ a i x out (update_success_bound a i x out hupdate) hupdate ha hx

theorem make3_points_canonical (a b c : Vector)
    (ha : VectorCanonical a) (hb : VectorCanonical b) (hc : VectorCanonical c) :
    StatementPointsCanonical (Array.make 3#usize [a,b,c]) := by
  intro k row hread i q hq
  have hkbound := index_success_bound (Array.make 3#usize [a,b,c] : StatementPoints) k row hread
  have hthree : (3#usize).val = 3 := by decide
  have hkcases : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 := by omega
  rcases hkcases with hk0 | hk1 | hk2
  · have hk : k = 0#usize := UScalar.eq_of_val_eq (by simpa using hk0)
    subst k
    change Result.ok a = Result.ok row at hread
    have he : a = row := Result.ok.inj hread
    subst row
    exact raw_read_canonical a i q ha hq
  · have hk : k = 1#usize := UScalar.eq_of_val_eq (by simpa using hk1)
    subst k
    change Result.ok b = Result.ok row at hread
    have he : b = row := Result.ok.inj hread
    subst row
    exact raw_read_canonical b i q hb hq
  · have hk : k = 2#usize := UScalar.eq_of_val_eq (by simpa using hk2)
    subst k
    change Result.ok c = Result.ok row at hread
    have he : c = row := Result.ok.inj hread
    subst row
    exact raw_read_canonical c i q hc hq

/-- Accepted-run property of the actual producer: the carry result and both
complement writes are derived from this same execution, not supplied as premises. -/
theorem statement_points_success_canonical (z : Vector) (points : StatementPoints)
    (hz : VectorCanonical z)
    (hsource : state_only_prefix.r0.statement_points z = .ok points) :
    StatementPointsCanonical points := by
  unfold state_only_prefix.r0.statement_points state_only_prefix.state_only_statement_points at hsource
  obtain ⟨s, hs, hsource⟩ := bind_success_inv _ _ _ hsource
  obtain ⟨iter, hiter, hsource⟩ := bind_success_inv _ _ _ hsource
  obtain ⟨successor, hsuccessor, hsource⟩ := bind_success_inv _ _ _ hsource
  obtain ⟨q, hq, hsource⟩ := bind_success_inv _ _ _ hsource
  obtain ⟨q1, hq1, hsource⟩ := bind_success_inv _ _ _ hsource
  obtain ⟨absorption, ha, hsource⟩ := bind_success_inv _ _ _ hsource
  obtain ⟨q2, hq2, hsource⟩ := bind_success_inv _ _ _ hsource
  obtain ⟨q3, hq3, hsource⟩ := bind_success_inv _ _ _ hsource
  obtain ⟨absorption1, ha1, hsource⟩ := bind_success_inv _ _ _ hsource
  have hone : CanQ (toProbeQ field.QM31.ONE) := by
    change AspisR1S9ConstructorV3Loop1CellCanonicalV1.CanQ
      (AspisR1S9ConstructorV3Loop1CellCanonicalV1.toProbeQ field.QM31.ONE)
    exact AspisR1S9ConstructorV3Loop1CellCanonicalV1.one_canonical
  have hsuccessorCan := AspisR1S9ConstructorV3SuccessorCarryLoopCanonicalV1.carry_loop_success_canonical
    z z successor iter field.QM31.ONE hz hz hone hsuccessor
  have hqCan := raw_read_canonical z 7#usize q hz hq
  have hq1Can : CanQ (toProbeQ q1) := by
    simpa only [toProbeQ, AspisR1S9ConstructorV3QMAddSubCanonicalV1.toProbeQM] using
      AspisR1S9ConstructorV3QMAddSubCanonicalV1.qm_sub_success_canonical field.QM31.ONE q q1 hone hqCan hq1
  have haCan := vector_update_canonical z absorption 7#usize q1 hz hq1Can ha
  have hq2Can := raw_read_canonical absorption 6#usize q2 haCan hq2
  have hq3Can : CanQ (toProbeQ q3) := by
    simpa only [toProbeQ, AspisR1S9ConstructorV3QMAddSubCanonicalV1.toProbeQM] using
      AspisR1S9ConstructorV3QMAddSubCanonicalV1.qm_sub_success_canonical field.QM31.ONE q2 q3 hone hq2Can hq3
  have ha1Can := vector_update_canonical absorption absorption1 6#usize q3 haCan hq3Can ha1
  have he : Array.make 3#usize [z,successor,absorption1] = points := Result.ok.inj hsource
  rw [← he]
  exact make3_points_canonical z successor absorption1 hz hsuccessorCan ha1Can

#print axioms vector_update_canonical
#print axioms make3_points_canonical
#print axioms statement_points_success_canonical
end AspisR1S9ConstructorV3StatementProducerCanonicalV1
