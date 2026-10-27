import Op3I_ParseLaws
import RPz7_RowShape_InstalledSlots
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.Op3I_Install
open AspisR1CurrentCaller

def currentVariant : Op3I_Source.transport.Variant → transport.Variant
  | .S1 => .S1 | .S2 => .S2 | .D => .D

def currentError : Op3I_Source.verifier.Error → verifier.Error
  | .Parse => .Parse | .Semantic => .Semantic | .Transcript => .Transcript
  | .Relation => .Relation | .Merkle => .Merkle | .Query => .Query
  | .Checkpoint => .Checkpoint | .Allocation => .Allocation

/-- Concrete existing Aeneas emission, with total pure-library implementations
and nominal carrier transport only. No caller success is built into the body. -/
def sourceBody (proof : Slice U8) : Result (core.result.Result transport.Variant verifier.Error) := do
  let r ← Op3I_Source.verifier.candidate.parse_shape Op3I_Std.ops proof
  match r with
  | .Err e => ok (.Err (currentError e))
  | .Ok v => ok (.Ok (currentVariant v))

def install (ops : Ops) : Ops := {ops with op3 := sourceBody}

theorem zero_tail (xs : List U8) (h : xs.any (fun x => x != 0#u8) = false) :
    xs = List.replicate xs.length 0#u8 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.any_cons,Bool.or_eq_false_iff] at h
    have hx : x = 0#u8 := by simpa using h.1
    simpa only [List.length_cons,List.replicate_succ,hx] using
      congrArg (List.cons 0#u8) (ih h.2)

theorem header_of_success (proof : Slice U8) (variant : transport.Variant)
    (success : sourceBody proof = ok (.Ok variant)) :
    variant = .S2 ∧ OraclePortHeader.accepts (MultiproofConeCanonical.bytesOf proof.val) = true := by
  unfold sourceBody at success
  obtain ⟨result,call,success⟩ := Op3I_ParseLaws.bind_success _ _ _ success
  cases result with
  | Err e => cases success
  | Ok v =>
    obtain ⟨variant2,length,magic,tag,tail⟩ := Op3I_ParseLaws.source_success proof v call
    subst v
    cases success
    refine ⟨rfl,(OraclePortHeader.accepts_iff _).mpr ?_⟩
    have zeros := zero_tail ((proof.val.drop 9).take 7) tail
    have tailLength : ((proof.val.drop 9).take 7).length = 7 := by
      simp only [List.length_take,List.length_drop,length]
      decide
    rw [tailLength] at zeros
    refine ⟨?_,?_,?_,?_⟩
    · simpa only [MultiproofConeCanonical.bytesOf,List.length_map] using length
    · unfold MultiproofConeCanonical.bytesOf
      rw [← List.map_take,magic]
      simp only [Op3I_Source.compact.MAGIC,OraclePortHeader.magic]
      rfl
    · unfold MultiproofConeCanonical.bytesOf
      rw [List.getElem?_map,tag]
      rfl
    · unfold MultiproofConeCanonical.bytesOf
      rw [← List.map_drop,← List.map_take,zeros,List.map_replicate]
      rfl

theorem installed_slot (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls) :
    (RowShape_InstalledSlots.verifierOps (install ops) B std).op3 = sourceBody := rfl

theorem other_slots (ops : Ops) :
    {install ops with op3 := ops.op3} = ops := by cases ops; rfl

#print axioms zero_tail
#print axioms header_of_success
#print axioms installed_slot
#print axioms other_slots
end AspisR1.Op3I_Install
end
