import NFO_ReadModel
set_option autoImplicit false
noncomputable section
namespace NFO_ReadAccepted
open Aeneas Aeneas.Std Result NFO_ReadModel

theorem accepted {Key : Type} [DecidableEq Key] (selected : Key)
    (cpi : core.result.Result Unit AdapterRw.solana_program_error.ProgramError)
    (returned : Option (Key × Bytes))
    (decode : Bytes → Result (core.result.Result Output DecodeError))
    (value : Accepted) (events : List Event)
    (success : run selected cpi returned decode = ok (.Ok value,events)) :
    cpi = .Ok () ∧ ∃ bytes,
      returned = some (selected,bytes) ∧ bytes.length = 792 ∧
      decode bytes = ok (.Ok value.value) ∧ value.bytes = bytes ∧
      events = [.clear,.invoke,.read,.decode] := by
  cases cpi with
  | Err e => cases success
  | Ok unit =>
    cases unit
    refine ⟨rfl, ?_⟩
    cases returned with
    | none => cases success
    | some pair =>
      rcases pair with ⟨program,bytes⟩
      by_cases hp : program ≠ selected
      · simp only [run, if_pos hp] at success
        cases success
      · have heq : program = selected := not_not.mp hp
        subst program
        by_cases hl : bytes.length ≠ 792
        · simp only [run, ne_eq, not_true_eq_false, if_false, if_pos hl] at success
          cases success
        · have width : bytes.length = 792 := not_not.mp hl
          simp only [run, ne_eq, not_true_eq_false, if_false, width] at success
          cases hd : decode bytes with
          | fail e => simp only [hd, bind_tc_fail] at success; cases success
          | div => simp only [hd, bind_tc_div] at success; cases success
          | ok decoded =>
            cases decoded with
            | Err e => simp only [hd, bind_tc_ok] at success; cases success
            | Ok output =>
              simp only [hd, bind_tc_ok] at success
              have pairEq := Result.ok.inj success
              have recEq := core.result.Result.Ok.inj (congrArg Prod.fst pairEq)
              have eventsEq := congrArg Prod.snd pairEq
              exact ⟨bytes,rfl,width,by rw [← recEq]; exact hd,
                congrArg Accepted.bytes recEq.symm,eventsEq.symm⟩
#print axioms accepted
end NFO_ReadAccepted
