import NGJ_VERIFIER_IMPORT
set_option autoImplicit false
noncomputable section
namespace NGL_FirstDecoded
open Aeneas Aeneas.Std Result
abbrev PE := AdapterRw.solana_program_error.ProgramError
abbrev VE := AdapterRw.aspis_r1_cost_probe.verifier.Error
abbrev Public := AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
abbrev V := alloc.vec.Vec U8
/-- The actual emitted body: observer is derived, not an accepted-run premise.
    Error callback and arbitrary complete tx1 Result stay visible in order. -/
theorem schedule (ops : AdapterRw.Ops) (public : Public)
    (publicBytes proof : Slice U8) (split : Usize) :
    AdapterRw.first_decoded ops public publicBytes proof split =
      (do let r ← ops.op10 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
            public publicBytes proof split () none
          core.result.Result.map_err (BuiltinFnOnce VE PE) r ops.op44) := rfl

def mapped (r : core.result.Result V VE) : core.result.Result V PE :=
  match r with | .Ok v => .Ok v | .Err _ => .Err .InvalidInstructionData

def installError (ops : AdapterRw.Ops) : AdapterRw.Ops :=
  {ops with op44 := fun _ => ok .InvalidInstructionData}

theorem mapped_result (ops : AdapterRw.Ops) (public : Public)
    (publicBytes proof : Slice U8) (split : Usize) :
    AdapterRw.first_decoded (installError ops) public publicBytes proof split =
      (do let r ← ops.op10
            (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (installError ops))
            public publicBytes proof split () none
          ok (mapped r)) := by
  rw [schedule]
  cases h : ops.op10
      (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (installError ops))
      public publicBytes proof split () none with
  | fail e => rfl
  | div => rfl
  | ok r => cases r <;> rfl
#print axioms schedule
#print axioms mapped_result
end NGL_FirstDecoded
