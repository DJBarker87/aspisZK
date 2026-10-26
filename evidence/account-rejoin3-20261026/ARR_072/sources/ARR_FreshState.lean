import ARR_OffPath
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARR_FreshState
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw

/-- A valid native slice-of-slices for one 32-byte message. -/
def parts (s : State) : SdkC_Source.Parts :=
  ⟨[⟨(encodeState s).val,by have size := (encodeState s).property; scalar_tac⟩],by simp; scalar_tac⟩

theorem flatten_parts (s : State) : flatten (parts s) = bytes s := by
  simp only [parts,flatten,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    encodeState,List.map_map,Function.comp_def,byte_roundtrip,List.map_id_fun]

/-- Cardinality transport only; never enumerate the 256^32 oracle states. -/
theorem fresh (log : List Bytes) (bound : log.length < Fintype.card State) :
    ∃ s : State, bytes s ∉ log := by
  classical
  by_contra none
  have all : ∀ s : State, bytes s ∈ log := by
    simpa only [not_exists,not_not] using none
  have injection : Function.Injective bytes := fun _ _ h => List.ofFn_injective h
  have subset : (Finset.univ.image bytes : Finset Bytes) ⊆ log.toFinset := by
    intro x member
    obtain ⟨s,_,rfl⟩ := Finset.mem_image.mp member
    exact List.mem_toFinset.mpr (all s)
  have count := (Finset.card_le_card subset).trans (List.toFinset_card_le log)
  rw [Finset.card_image_of_injective _ injection,Finset.card_univ] at count
  omega

/-- Sufficient condition for a fixed native hash to defeat a global all-world
factory: it returns on all 32-byte messages, and one accepted run uses fewer
than 256^32 issued addresses. No source success/error case is filtered. -/
theorem no_factory {X : Type} (p : Program Bytes State X) (accepts : X → Prop)
    (H : Bytes → State) (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (accepted : accepts (eval H p).2)
    (bound : (eval H p).1.length < Fintype.card State)
    (return32 : ∀ s : State, ∃ digest, hashv (parts s) = .ok digest) :
    ¬ ∀ K : Bytes → State, accepts (eval K p).2 →
      ∃ sha256 : Bytes → State, S2W_ExtractionBoundary.P1 sha256 K ∧
        S2W_ExtractionBoundary.RuntimeSyscall hashv sha256 := by
  intro factory
  obtain ⟨s,unused⟩ := fresh ((eval H p).1.map Prod.fst) (by simpa only [List.length_map] using bound)
  obtain ⟨digest,returned⟩ := return32 s
  have forced := ARR_OffPath.factory_forces_reads p accepts H hashv accepted factory (parts s) digest returned
  rw [flatten_parts] at forced
  exact unused forced

#print axioms flatten_parts
#print axioms fresh
#print axioms no_factory
end AspisR1.ARR_FreshState
end
