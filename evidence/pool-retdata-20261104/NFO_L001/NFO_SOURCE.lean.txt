import NEU_EmitModel
set_option autoImplicit false
noncomputable section
namespace NFO_ReadModel
open Aeneas Aeneas.Std Result
abbrev Output := NEU_EmitModel.Output
abbrev DecodeError := NEU_EmitModel.Error
abbrev Bytes := List U8
inductive Error where
  | cpi : AdapterRw.solana_program_error.ProgramError → Error
  | missing | program | data
inductive Event where
  | clear | invoke | read | decode
structure Accepted where
  value : Output
  bytes : Bytes

def run {Key : Type} [DecidableEq Key] (selected : Key)
    (cpi : core.result.Result Unit AdapterRw.solana_program_error.ProgramError)
    (returned : Option (Key × Bytes))
    (decode : Bytes → Result (core.result.Result Output DecodeError)) :
    Result (core.result.Result Accepted Error × List Event) :=
  match cpi with
  | .Err e => ok (.Err (.cpi e), [.clear,.invoke])
  | .Ok () =>
    match returned with
    | none => ok (.Err .missing, [.clear,.invoke,.read])
    | some (program,bytes) =>
      if program ≠ selected then ok (.Err .program, [.clear,.invoke,.read])
      else if bytes.length ≠ 792 then ok (.Err .data, [.clear,.invoke,.read])
      else do
        let decoded ← decode bytes
        match decoded with
        | .Err _ => ok (.Err .data, [.clear,.invoke,.read,.decode])
        | .Ok value => ok (.Ok ⟨value,bytes⟩, [.clear,.invoke,.read,.decode])

theorem cpi_error {Key : Type} [DecidableEq Key] (selected : Key)
    (e : AdapterRw.solana_program_error.ProgramError) (returned : Option (Key × Bytes))
    (decode : Bytes → Result (core.result.Result Output DecodeError)) :
    run selected (.Err e) returned decode = ok (.Err (.cpi e), [.clear,.invoke]) := rfl

theorem missing {Key : Type} [DecidableEq Key] (selected : Key)
    (decode : Bytes → Result (core.result.Result Output DecodeError)) :
    run selected (.Ok ()) none decode = ok (.Err .missing, [.clear,.invoke,.read]) := rfl

theorem wrong_program {Key : Type} [DecidableEq Key] (selected program : Key)
    (bytes : Bytes) (decode : Bytes → Result (core.result.Result Output DecodeError))
    (different : program ≠ selected) :
    run selected (.Ok ()) (some (program,bytes)) decode =
      ok (.Err .program, [.clear,.invoke,.read]) := by
  simp only [run, if_pos different]

theorem wrong_length {Key : Type} [DecidableEq Key] (selected : Key)
    (bytes : Bytes) (decode : Bytes → Result (core.result.Result Output DecodeError))
    (length : bytes.length ≠ 792) :
    run selected (.Ok ()) (some (selected,bytes)) decode =
      ok (.Err .data, [.clear,.invoke,.read]) := by
  simp only [run, ne_eq, not_true_eq_false, if_false, if_pos length]

theorem decoded {Key : Type} [DecidableEq Key] (selected : Key)
    (bytes : Bytes) (decode : Bytes → Result (core.result.Result Output DecodeError))
    (value : Output) (length : bytes.length = 792)
    (decoded : decode bytes = ok (.Ok value)) :
    run selected (.Ok ()) (some (selected,bytes)) decode =
      ok (.Ok ⟨value,bytes⟩, [.clear,.invoke,.read,.decode]) := by
  simp only [run, ne_eq, not_true_eq_false, if_false, length, decoded, bind_tc_ok]

#print axioms cpi_error
#print axioms missing
#print axioms wrong_program
#print axioms wrong_length
#print axioms decoded
end NFO_ReadModel
