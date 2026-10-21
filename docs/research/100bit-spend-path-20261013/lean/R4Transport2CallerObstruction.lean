import ExtractedPreparedModel

/-! Interface countermodels, not bugs in the shipped sampler. These identify
why a successful Prepared boundary call cannot close the remaining byte/state
joins without binding the boundary to its source implementation. -/
set_option autoImplicit false
namespace AspisR1PublicPreparation.R4Transport2CallerObstruction
open Aeneas Aeneas.Std Result

def withQueryState (B : PreparedModel.Boundaries) (queries : Array U32 22#usize)
    (state : Array U8 32#usize) : PreparedModel.Boundaries :=
  { B with queries := fun {Hash} _ self _ _ => ok (.Ok queries,{self with state}) }

theorem arbitrary_query_state {Hash : Type} (B : PreparedModel.Boundaries)
    (D : aspis_core.Digest32 Hash) (self : transcript.Transcript Hash)
    (payload : Slice U8) (queries : Array U32 22#usize) (state : Array U8 32#usize) :
    (withQueryState B queries state).queries D self 31#u8 payload =
      ok (.Ok queries,{self with state}) := rfl

/-- Any supposed state property obtained universally from this interface
must hold for every possible returned state. No digest or scan is consulted. -/
theorem universal_query_state_property {Hash : Type} (B : PreparedModel.Boundaries)
    (D : aspis_core.Digest32 Hash) (self : transcript.Transcript Hash)
    (payload : Slice U8) (queries : Array U32 22#usize)
    (property : Array U8 32#usize → Prop)
    (h : ∀ (B' : PreparedModel.Boundaries) after,
      B'.queries D self 31#u8 payload = ok (.Ok queries,after) → property after.state) :
    ∀ state, property state := by
  intro state
  exact h (withQueryState B queries state) {self with state}
    (arbitrary_query_state B D self payload queries state)

/-- The retained toBytes boundary does not imply canonical serialization,
even for a fixed inactive field element. -/
theorem arbitrary_inactive_bytes (B : PreparedModel.Boundaries)
    (inactive : aspis_core.field.WideExact) (bytes : Array U8 32#usize) :
    ∃ B' : PreparedModel.Boundaries, B'.toBytes inactive = ok bytes := by
  exact ⟨{ B with toBytes := fun _ => ok bytes },rfl⟩

#print axioms arbitrary_query_state
#print axioms universal_query_state_property
#print axioms arbitrary_inactive_bytes
end AspisR1PublicPreparation.R4Transport2CallerObstruction
