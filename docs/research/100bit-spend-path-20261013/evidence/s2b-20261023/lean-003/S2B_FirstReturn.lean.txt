import S2SdkReadyStatementV1

/-! Local source-cut transport, not a construction of a native execution.
`E` indexes one externally supplied execution. All cut projections below are
read from that same index. The native-to-extracted child equation and original
read frames remain explicit premises; SDK library trust does not imply them. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2B_FirstReturn
open AspisS2OwnedStage1 AspisS2OwnedStage1.SdkReference

abbrev Checkpoint := alloc.vec.Vec U8
abbrev Error := solana_program_error.ProgramError
abbrev ChildResult := Result (core.result.Result Checkpoint Error)

/-- The source's `?` followed by its length rejection. The value is retained
for reasoning about the later copy; this does not model the copy or cleanup. -/
def lengthGate (child : ChildResult) (expected : Nat) :
    Result (core.result.Result Checkpoint Error) := do
  let r ← child
  match r with
  | .Err e => ok (.Err e)
  | .Ok cp =>
      if cp.val.length = expected then
        ok (.Ok cp)
      else
        ok (.Err .InvalidAccountData)

/-- This is a view of a cut, not a certificate that any native execution
reaches it. No source refinement is asserted by constructing this record. -/
structure CutView (Execution : Type) where
  statement : Execution → ReadyStatement.Statement
  publicRead : Execution → Slice U8
  proofRead : Execution → Slice U8
  split : Execution → Usize
  returned : Execution → ChildResult

/-- Invert just the child return and the subsequent length check. The witness
is the checkpoint in THIS return, not a second successful child execution. -/
theorem invert_length (child : ChildResult) (expected : Nat)
    (accepted : ∃ cp, lengthGate child expected = ok (.Ok cp)) :
    ∃ cp, child = ok (.Ok cp) ∧ cp.val.length = expected := by
  obtain ⟨out,h⟩ := accepted
  cases child with
  | fail e => simp only [lengthGate,bind_tc_fail] at h; cases h
  | div => simp only [lengthGate,bind_tc_div] at h; cases h
  | ok r =>
    cases r with
    | Err e => cases h
    | Ok cp =>
      by_cases size : cp.val.length = expected
      · exact ⟨cp,rfl,size⟩
      · simp only [lengthGate,bind_tc_ok,if_neg size] at h
        cases h

/-- Fixed original arguments are transported to current tx1. The premises
`childTransport`, `publicFrame`, `proofFrame`, and `splitFrame` must come from
one native prefix/continuation proof; they are not supplied by this theorem.
The semantic getter is discharged for the actual complete statement. -/
theorem transport {Execution : Type} (view : CutView Execution) (E : Execution)
    (ops : SdkReference.Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (originalPublic originalProofSuffix : Slice U8) (ten : Bool)
    (publicFrame : view.publicRead E = originalPublic)
    (proofFrame : view.proofRead E = originalProofSuffix)
    (splitFrame : view.split E = ReadyCaller.splitIndex ten)
    (childTransport : view.returned E =
      first_decoded (Installation.install ops verifierOps)
        (ReadyStatement.publicOf (view.statement E))
        (view.publicRead E) (view.proofRead E) (view.split E))
    (checkpointAccountLength : Nat) (admittedLength : checkpointAccountLength = 1768)
    (accepted : ∃ cp, lengthGate (view.returned E) checkpointAccountLength = ok (.Ok cp)) :
    ∃ cp,
      view.returned E = ok (.Ok cp) ∧ cp.val.length = 1768 ∧
      SdkReference.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
        (view.statement E) = ok (ReadyStatement.publicOf (view.statement E)) ∧
      first_decoded (Installation.install ops verifierOps)
        (ReadyStatement.publicOf (view.statement E)) originalPublic originalProofSuffix
        (ReadyCaller.splitIndex ten) = ok (.Ok cp) ∧
      AspisR1CurrentCaller.verifier.candidate.tx1 verifierOps
        (SourceInstallation.currentDigest
          (SolanaDigest.Insts.Aspis_coreDigestDigest32 (Installation.install ops verifierOps)))
        (CurrentCarrier.toCurrentPublic (ReadyStatement.publicOf (view.statement E)))
        originalPublic originalProofSuffix (ReadyCaller.splitIndex ten) () none = ok (.Ok cp) := by
  obtain ⟨cp,hreturned,hsize⟩ := invert_length (view.returned E) checkpointAccountLength accepted
  have first := childTransport.symm.trans hreturned
  rw [publicFrame,proofFrame,splitFrame] at first
  exact ⟨cp,hreturned,hsize.trans admittedLength,ReadyStatement.public_total _,first,
    Installation.first_success ops verifierOps _ _ _ _ cp first⟩

#print axioms invert_length
#print axioms transport
end AspisR1.S2B_FirstReturn
