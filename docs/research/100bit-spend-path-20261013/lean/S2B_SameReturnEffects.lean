import S2B_OriginalInputs
import S2B_Syscalls
import S2B_ChildEffects
import S2B_LeadCarriers

/-! Conditional composition on ONE execution index. The source cut transport,
reified child run, erasure equation and per-call oracle law remain explicit.
In particular erasure is not an assertion of native trace equality: the native
certificate must separately identify the child Code's run and log with E. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2B_SameReturnEffects
open AspisS2OwnedStage1 AspisS2OwnedStage1.SdkReference
open AspisV8R19.DuplexFrames AspisR1DigestLogCarrier
open CheckpointBytes5Effect

abbrev digestFor (ops : SdkReference.Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (hashv : Parts → Result Digest) :=
  S2B_Syscalls.stage2Digest (S2B_Syscalls.withSyscalls ops hashv) verifierOps

/-- Same returned Vec, length1768, current child with None, same reified child
return, and the actual ordered log's consistency. This is an integration lemma,
not evidence that native acceptance supplies any of its refinement premises. -/
theorem same_return {Execution : Type} (view : S2B_FirstReturn.CutView Execution) (E : Execution)
    (ops : SdkReference.Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (hashv : Execution → Parts → Result Digest)
    (H : Bytes → AspisR1DigestLogCarrier.State)
    (originalPublic originalProofSuffix : Slice U8) (ten : Bool)
    (publicFrame : view.publicRead E = originalPublic)
    (proofFrame : view.proofRead E = originalProofSuffix)
    (splitFrame : view.split E = ReadyCaller.splitIndex ten)
    (childTransport : view.returned E =
      SdkReference.first_decoded
        (Installation.install (S2B_Syscalls.withSyscalls ops (hashv E)) verifierOps)
        (ReadyStatement.publicOf (view.statement E))
        (view.publicRead E) (view.proofRead E) (view.split E))
    (checkpointAccountLength : Nat) (admittedLength : checkpointAccountLength = 1768)
    (accepted : ∃ cp, S2B_FirstReturn.lengthGate (view.returned E) checkpointAccountLength = ok (.Ok cp))
    (child : Execution → Code (core.result.Result (alloc.vec.Vec U8)
      solana_program_error.ProgramError))
    (before after : Log)
    (outcome : core.result.Result (alloc.vec.Vec U8) solana_program_error.ProgramError)
    (effectRun : run (digestFor ops verifierOps (hashv E)) () (child E) before = ok (outcome,after))
    (erases : erase (digestFor ops verifierOps (hashv E)) () (child E) = view.returned E)
    (oracle : ∀ parts, hashv E parts = ok
      (AspisV8R19.SqueezeOracleBridge.encodeState (H (flatten parts))))
    (initial : Consistent H (S2B_LeadCarriers.observe before)) :
    ∃ cp, view.returned E = ok (.Ok cp) ∧ cp.val.length = 1768 ∧
      AspisR1CurrentCaller.verifier.candidate.tx1 verifierOps
        (SourceInstallation.currentDigest
          (SolanaDigest.Insts.Aspis_coreDigestDigest32
            (Installation.install (S2B_Syscalls.withSyscalls ops (hashv E)) verifierOps)))
        (CurrentCarrier.toCurrentPublic (ReadyStatement.publicOf (view.statement E)))
        originalPublic originalProofSuffix (ReadyCaller.splitIndex ten) () none = ok (.Ok cp) ∧
      run (digestFor ops verifierOps (hashv E)) () (child E) before = ok (.Ok cp,after) ∧
      Consistent H (S2B_LeadCarriers.observe after) := by
  obtain ⟨cp,returned,size,_,_,current⟩ := S2B_FirstReturn.transport view E
    (S2B_Syscalls.withSyscalls ops (hashv E)) verifierOps originalPublic originalProofSuffix ten
    publicFrame proofFrame splitFrame childTransport checkpointAccountLength admittedLength accepted
  have value := run_success (digestFor ops verifierOps (hashv E)) () (child E) before after outcome effectRun
  have same := Result.ok.inj (value.symm.trans (erases.trans returned))
  subst outcome
  refine ⟨cp,returned,size,current,effectRun,?_⟩
  exact S2B_LeadCarriers.ordered_calls E (digestFor ops verifierOps (hashv E)) () H child before after
    (.Ok cp) (S2B_LeadCarriers.digest_children E hashv H oracle) initial effectRun

#print axioms same_return
end AspisR1.S2B_SameReturnEffects
