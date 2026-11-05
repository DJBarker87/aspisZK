import NHF_ViewFinish
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHF_ViewResult
open Aeneas Aeneas.Std Result AspisR1SelectedWideViewV1
open StrictWideByteCodec WideParserArrayHalves NGV_ByteWindow

def input (proof : Slice U8) (size : 10055 ≤ proof.val.length) : Array U8 32#usize :=
 ⟨(select proof 7495 32).val,by
   have h:=select_length proof 7495 32 (by omega)
   simpa only [UScalar.ofNatCore_val_eq] using h⟩

def model (proof semantic y1 : Slice U8) (size : 10055 ≤ proof.val.length) :
 core.result.Result verifier.View verifier.Error :=
 match decodeWideLE (arrayBytes32 (input proof size)) with
 | none => .Err .Parse
 | some wide => .Ok (NHF_ViewFinish.value proof semantic y1
     (parserCarrier (CandidateWideParserRefinement.limbsToCandidate wide)) size)

/-- Entire emitted view result on the caller's original byte backing, including
noncanonical rejection. The decoder value is computed, never supplied as a
root hypothesis. All borrowed fields refer to those original byte windows. -/
theorem result (proof semantic y1 : Slice U8) (size : 10055 ≤ proof.val.length) :
 verifier.candidate.wide_view proof semantic y1 = ok (model proof semantic y1 size) := by
 rw [NHF_ViewCut.source]
 unfold NHF_ViewCut.range
 rw [read proof 7495#usize 7527#usize (by change 7495≤7527 ∧ 7527≤_;omega),bind_tc_ok]
 have same : Array.to_slice (input proof size)=select proof 7495 32 := rfl
 rw [←same,NHF_ViewDecoder.result,bind_tc_ok]
 cases decoded : decodeWideLE (arrayBytes32 (input proof size)) with
 | none =>
   simp only [Option.map_none,NHF_ViewCut.reject,model,decoded]
 | some wide =>
   simp only [Option.map_some,NHF_ViewCut.accepted,NHF_ViewFinish.result,model,decoded]

/-- Immutable arguments and no runtime child calls: the leaf's observable
state frame and empty ordered-effect suffix are unchanged. -/
theorem result_state_effects {State Event : Type} (state : State)
 (proof semantic y1 : Slice U8) (size : 10055 ≤ proof.val.length) :
 (do let out ← verifier.candidate.wide_view proof semantic y1
     ok (out,state,([] : List Event))) =
 ok (model proof semantic y1 size,state,([] : List Event)) := by
 rw [result proof semantic y1 size]
 rfl
#print axioms result
#print axioms result_state_effects
end AspisR1.NHF_ViewResult
end
