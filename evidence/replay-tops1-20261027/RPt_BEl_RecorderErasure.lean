import RPt_BEl_RawBackend
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEl_RecorderErasure
open Aeneas Aeneas.Std Result SdkC_Source

def forget (history : BEl_Recorder.History) : Log := history.filterMap fun attempt =>
  attempt.returned.map (fun answer => ⟨attempt.parts,answer⟩)

/-- Only completed histories have this left inverse. Pending native attempts
must never be dropped by applying it outside the returned-call domain. -/
theorem completed (before : Log) : forget (BEl_Recorder.completed before) = before := by
  induction before with
  | nil => rfl
  | cons query tail ih =>
    simpa only [forget,BEl_Recorder.completed,List.map_cons,List.filterMap_cons,
      Option.map_some] using congrArg (List.cons query) ih

/-- Exact source log recovered from a returned raw-backend reference run. -/
theorem reference {S A : Type} (backend : Parts → S → Digest × S)
    (code : Code A) (state : S) (before : Log) :
    forget (BEl_RawBackend.run backend code state (BEl_Recorder.completed before)).2.2 =
      (BEf_Carrier.run (BEl_RawBackend.call backend) code state before).2.2 := by
  rw [BEl_RawBackend.correspondence]
  exact completed _

/-- A pending attempt is observable and is explicitly outside erasure's
injective domain. This prevents interpreting forget as a physical-prefix proof. -/
theorem pending (parts : Parts) :
    forget [⟨parts,none⟩] = [] ∧ [⟨parts,none⟩] ≠ ([] : BEl_Recorder.History) := by
  exact ⟨rfl,List.cons_ne_nil _ _⟩

#print axioms completed
#print axioms reference
#print axioms pending
end AspisR1.BEl_RecorderErasure
end
