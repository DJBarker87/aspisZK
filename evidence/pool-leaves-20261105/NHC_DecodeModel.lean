import NHC_HintDecoderDomain
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace NHC_DecodeModel
abbrev Request := AspisR1.NFY_JHd_RequestNative.Request
abbrev Error := AdapterRw.solana_program_error.ProgramError
abbrev Hints := NHC_Hints.pair_forest.PoolV1PairForestTerminalBumpHintsV1
abbrev Output := Request × Hints
/-- Value interpretation of the first three account reads, after the decoder.
Box allocation and physical account identity are separate native obligations. -/
def afterDecode (d : core.result.Result Request AspisR1.NFY_JHd_RequestNative.FormatError)
    (count : Nat) (hints : Hints) : core.result.Result Output Error :=
  match d with
  | .Err _ => .Err .InvalidInstructionData
  | .Ok request => if count < 3 then .Err .NotEnoughAccountKeys else .Ok (request,hints)
/-- Actual emitted strip, the canonical CLOSED S decoder, then the account head.
This is a model composition, not a production AccountInfo interpretation. -/
def run (input : Slice U8) (count : Nat) : Result (core.result.Result Output Error) := do
  let stripped ← NHC_Hints.pair_forest.split_pair_forest_terminal_bump_hints_v1 input
  match stripped with
  | .Err e => ok (.Err e)
  | .Ok (body,hints) =>
    let decoded ← AspisR1.NFY_JHd_RequestNative.decode body
    ok (afterDecode decoded count hints)

theorem decoder_error (e : AspisR1.NFY_JHd_RequestNative.FormatError) (count : Nat) (h : Hints) :
    afterDecode (.Err e) count h = .Err .InvalidInstructionData := rfl
#print axioms decoder_error

theorem short (input : Slice U8) (count : Nat) (h : input.val.length < 4) :
    run input count = ok (.Err .InvalidInstructionData) := by
  simp only [run,NHC_HintsTotal.short input h,bind_tc_ok]
#print axioms short
end NHC_DecodeModel
