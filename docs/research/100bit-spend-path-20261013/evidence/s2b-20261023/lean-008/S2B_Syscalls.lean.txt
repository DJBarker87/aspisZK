import S2B_FirstReturn
import Stage2ContinuationTypes

/-! Source value interpretation only. Error logging is a separate effect. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2B_Syscalls
open AspisS2OwnedStage1 AspisS2OwnedStage1.SdkReference
abbrev Parts := Slice (Slice U8)
abbrev Digest := Array U8 32#usize

/-- Source lib.rs:10-16 and :40. The hash backend remains explicit. Error
logging remains a separate native obligation; the value-level map is fixed here. -/
def withSyscalls (ops : SdkReference.Ops) (hashv : Parts → Result Digest) : SdkReference.Ops :=
  {ops with
    op10 := (fun _ parts => hashv parts),
    op11 := fun _ => ok .InvalidInstructionData}

/-- After installing both concrete syscall fields, the remaining adapter Ops
seed has no influence. verifierOps and the digest backend are still explicit. -/
theorem adapter_seed_irrelevant {Execution : Type} (E : Execution)
    (ops other : SdkReference.Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (hashv : Execution → Parts → Result Digest) :
    Installation.install (withSyscalls ops (hashv E)) verifierOps =
      Installation.install (withSyscalls other (hashv E)) verifierOps :=
  Installation.install_dependencies _ _ verifierOps rfl rfl

/-- Exact return interpretation of each installed hash/error call. The error
message event is not part of this value-only equation. -/
theorem syscall_values {Execution : Type} (E : Execution) (ops : SdkReference.Ops)
    (verifierOps : AspisR1CurrentCaller.Ops)
    (hashv : Execution → Parts → Result Digest) (parts : Parts)
    (err : aspis_r1_cost_probe.verifier.Error) :
    (Installation.install (withSyscalls ops (hashv E)) verifierOps).op10 () parts = hashv E parts ∧
    (Installation.install (withSyscalls ops (hashv E)) verifierOps).op11 err =
      ok .InvalidInstructionData := ⟨rfl,rfl⟩

/-- Bridge the concrete installed digest's fields to the Stage2 trait carrier;
no new oracle law is introduced by changing the trait record. -/
def stage2Digest (ops : SdkReference.Ops) (verifierOps : AspisR1CurrentCaller.Ops) :
    AspisR1Stage2.aspis_core.digest.Digest32 Unit :=
  let d := SolanaDigest.Insts.Aspis_coreDigestDigest32 (Installation.install ops verifierOps)
  {coremarkerCopyInst := d.coremarkerCopyInst,
    digest := d.digest}

/-- The actual wrapper maps a reached current-child verifier error to the
source ProgramError. This value theorem does not erase or certify its msg! event. -/
theorem first_error {Execution : Type} (E : Execution) (ops : SdkReference.Ops)
    (verifierOps : AspisR1CurrentCaller.Ops)
    (hashv : Execution → Parts → Result Digest)
    (pub : Execution → Reachability.Public) (bytes proof : Execution → Slice U8)
    (split : Execution → Usize) (err : AspisR1CurrentCaller.verifier.Error)
    (child : AspisR1CurrentCaller.verifier.candidate.tx1 verifierOps
      (SourceInstallation.currentDigest
        (SolanaDigest.Insts.Aspis_coreDigestDigest32
          (Installation.install (withSyscalls ops (hashv E)) verifierOps)))
      (CurrentCarrier.toCurrentPublic (pub E)) (bytes E) (proof E) (split E) () none =
        ok (.Err err)) :
    SdkReference.first_decoded (Installation.install (withSyscalls ops (hashv E)) verifierOps)
      (pub E) (bytes E) (proof E) (split E) = ok (.Err .InvalidInstructionData) := by
  unfold SdkReference.first_decoded
  simp only [Installation.observer_none,bind_tc_ok]
  change (do
    let r ← SourceInstallation.currentChild verifierOps
      (SolanaDigest.Insts.Aspis_coreDigestDigest32
        (Installation.install (withSyscalls ops (hashv E)) verifierOps))
      (pub E) (bytes E) (proof E) (split E) () none
    SdkReference.core.result.Result.map_err
      (BuiltinFnOnce aspis_r1_cost_probe.verifier.Error solana_program_error.ProgramError) r
      (fun _ => ok solana_program_error.ProgramError.InvalidInstructionData)) = _
  unfold SourceInstallation.currentChild
  simp only [Option.map_none,child,bind_tc_ok]
  rfl

#print axioms adapter_seed_irrelevant
#print axioms syscall_values
#print axioms first_error
end AspisR1.S2B_Syscalls
