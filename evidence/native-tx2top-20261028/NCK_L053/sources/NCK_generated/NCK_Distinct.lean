import NCK_DistinctOuter
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCK_Distinct
open Aeneas Aeneas.Std Result
open _root_.AdapterRw.r1_pool_adapter.owned NCK_DistinctInner NCK_DistinctOuter
attribute [local instance] Classical.propDecidable
/-- Full Result, including duplicate rejection, for the actual emitted seven-
account loop. Comparison is the explicit primitive port law, not a new axiom. -/
theorem source (ops : _root_.AdapterRw.Ops) (a : Accounts) (comparison : Comparison ops) :
    require_distinct_accounts ops a = ok
      (if Remaining a 0 then .Ok () else
        .Err _root_.AdapterRw.solana_program_error.ProgramError.InvalidArgument) := by
  unfold require_distinct_accounts
  rw [NCK_DistinctOuter.source ops a 0#usize (by scalar_tac) comparison]
  change (do let r ← ok (if Remaining a 0 then none else
    some (core.result.Result.Err _root_.AdapterRw.solana_program_error.ProgramError.InvalidArgument))
    match r with | none => ok (.Ok ()) | some v => ok v) = _
  split <;> simp_all [bind_tc_ok]

theorem accepted (ops : _root_.AdapterRw.Ops) (a : Accounts) (comparison : Comparison ops)
    (success : require_distinct_accounts ops a = ok (.Ok ())) : Remaining a 0 := by
  rw [source ops a comparison] at success
  split at success
  · assumption
  · cases success
#print axioms source
#print axioms accepted
end AspisR1.NCK_Distinct
end
