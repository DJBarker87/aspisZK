import RPz7_RowShape_InstalledSlots
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.RowShape_SlotObstruction
open AspisR1CurrentCaller MultiproofConeCanonical OraclePortCompactDraft
open RowShape_InstalledSlots
open AspisV8R19.DuplexFrames
open RawCutTranscriptRun (ErasedPrefix)

/-- A permitted argument of the existing parameterized installation, not a
candidate source implementation or an adopted replacement. -/
def permissive (ops : Ops) : Ops :=
  {ops with op3 := fun _ => ok (.Ok .S1), op4 := fun _ => ok (.Ok ())}

def empty : Slice U8 := ⟨[], by simp⟩

/-- Installed shape can return even the wrong variant on arbitrary bytes. -/
theorem shape_arbitrary (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls) (proof : Slice U8) :
    (verifierOps (permissive ops) B std).op3 proof = ok (.Ok .S1) := rfl

/-- Installed scan can return success independently of the supplied bytes. -/
theorem scan_arbitrary (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls) (proof : Slice U8) :
    (verifierOps (permissive ops) B std).op4 proof = ok (.Ok ()) := rfl

theorem frozen_empty (tr : ErasedPrefix) :
    OraclePortStoredParserC4.parseReached (bytesOf empty.val) tr = none := by
  have header : OraclePortHeader.accepts (bytesOf empty.val) = false :=
    OraclePortHeader.rejects_wrong_length _ (by decide)
  simp only [OraclePortStoredParserC4.parseReached, parse, header, if_true,
    Option.bind_none]
  rfl

/-- No full parser-success law follows from this installed shape's successful
return alone. This is a local-call counterexample, not an accepted TX witness. -/
theorem shape_success_not_parser (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls) (tr : ErasedPrefix) :
    (verifierOps (permissive ops) B std).op3 empty = ok (.Ok .S1) ∧
    OraclePortStoredParserC4.parseReached (bytesOf empty.val) tr = none :=
  ⟨shape_arbitrary ops B std empty, frozen_empty tr⟩

/-- Symbolic padding places one noncanonical word at the first scan offset. -/
def badScan : Slice U8 :=
  ⟨List.replicate 7031 0#u8 ++ [255#u8,255#u8,255#u8,255#u8], by
    simp only [List.length_append,List.length_replicate,List.length_cons,List.length_nil]
    scalar_tac⟩

theorem badScan_segment : slice (bytesOf badScan.val) 7031 464 = [255,255,255,255] := by
  simp only [slice,bytesOf,badScan,List.map_append,List.map_replicate,
    List.map_cons,List.map_nil,List.drop_append,List.drop_replicate,
    List.length_replicate,Nat.sub_self,List.replicate_zero,List.nil_append,
    List.drop_zero]
  rfl

theorem badScan_rejected : ¬ scan (bytesOf badScan.val) := by
  intro good
  have first := good.1
  rw [badScan_segment] at first
  have word := first.2 0 (by decide)
  norm_num [canonical,slice,little] at word

/-- A concrete local-call counterexample to inferring full canonicality from
installed scan success. It does not assert whole-transaction acceptance. -/
theorem scan_success_not_canonical (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls) :
    (verifierOps (permissive ops) B std).op4 badScan = ok (.Ok ()) ∧
    ¬ scan (bytesOf badScan.val) :=
  ⟨scan_arbitrary ops B std badScan, badScan_rejected⟩

#print axioms shape_arbitrary
#print axioms scan_arbitrary
#print axioms frozen_empty
#print axioms shape_success_not_parser
#print axioms badScan_segment
#print axioms badScan_rejected
#print axioms scan_success_not_canonical
end AspisR1.RowShape_SlotObstruction
end
