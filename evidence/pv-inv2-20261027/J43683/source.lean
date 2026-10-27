import R1Z.PV_Inv_SourceInverseTrace
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_InverseList
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitNativeQ48 (source)
open AspisR1.ExtractedCurrentQM31Exact (decode)

def observed (chi : Old.Q) : List Old.Q → Result (List (Bool × Option field.QM31))
 | [] => ok []
 | v::vs => do
   let a ← PV_Inv_SourceInverseTrace.observedInverse chi v
   let rest ← observed chi vs
   ok (a::rest)

theorem all_success (chi : Old.Q) (hc : Canonical chi) (vs : List Old.Q)
    (canon : ∀ v ∈ vs, Canonical v) (safe : ∀ v ∈ vs, decode chi ≠ decode v) :
    ∃ inverses : List Old.Q,
      (∀ v ∈ inverses, Canonical v) ∧ inverses.length=vs.length ∧
      observed chi vs=ok (inverses.map (fun v => (false,some (source v)))) := by
  induction vs with
  | nil => exact ⟨[],by simp,rfl,rfl⟩
  | cons v vs ih =>
    obtain ⟨inv,hci,hi⟩ := PV_Inv_SourceInverseTrace.success chi v hc (canon v (by simp)) (safe v (by simp))
    obtain ⟨invs,hcis,hlen,his⟩ := ih (fun v hv => canon v (by simp [hv])) (fun v hv => safe v (by simp [hv]))
    refine ⟨inv::invs,?_,by simp only [List.length_cons,hlen],?_⟩
    · intro v hv
      rcases List.mem_cons.mp hv with he|he
      · subst v;exact hci
      · exact hcis v he
    · simp only [observed,hi,his,bind_tc_ok,List.map_cons]

#print axioms all_success
end R1Z.PV_Inv_InverseList
