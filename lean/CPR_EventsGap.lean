import CPR_DataPersistence
import S2X_RuntimeRetention
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPR_EventsGap
open AspisV8R19.DuplexFrames

def events (saved : Bytes) : List S2X.AccountEvent :=
  [.committedWrite 0 [],.committedWrite 0 saved]

/-- Identical endpoint images cannot certify an intervening event sequence.
This is a history-algebra countermodel, not an allowed-verifier-write claim. -/
theorem final_image_equal (saved : Bytes) :
    S2X.history (fun _ => saved) (events saved) = (fun _ => saved) := by
  funext key
  by_cases same : key = 0 <;> simp [events,S2X.history,S2X.applyEvent,same]

theorem not_protected (saved : Bytes) :
    ¬ (∀ event ∈ events saved, S2X.Preserves 0 event) := by
  intro safe
  have bad := safe (.committedWrite 0 []) (by simp [events])
  exact bad rfl

/-- With the actual key and event list retained, the desired protected history
cannot be manufactured even though every final data image is unchanged. -/
theorem no_actual_history (saved : Bytes) :
    ¬ ∃ history : S2X.CheckpointVersionBinding saved saved,
      history.key = 0 ∧ history.events = events saved := by
  rintro ⟨history,key,trace⟩
  apply not_protected saved
  intro event member
  have safe := history.noInterveningWrite event (by rw [trace]; exact member)
  simpa only [key] using safe

/-- The proposed runtime law itself holds, on a genuine adjacent pair and
ordinary key, in this endpoint-image countermodel. Source-event interpretation
remains an independent obligation even after the law is supplied. -/
theorem runtime_law (saved : Bytes) :
    CPR_DataPersistence.TwoTransactionLaw (fun _ _ : Unit => True) (fun _ _ : Unit => True)
      (fun _ _ => ⟨saved,1⟩) (fun _ _ => ⟨saved,1⟩) (fun _ => true)
      (fun _ _ => some saved) := by
  intro t u adjacent key eligible
  rfl

#print axioms final_image_equal
#print axioms not_protected
#print axioms no_actual_history
#print axioms runtime_law
end AspisR1.CPR_EventsGap
end
