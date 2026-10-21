import S2SdkOwnedModelV1
import S2OwnedSourceInstallationV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.Installation
open SdkReference

def stdSliceArrayEq {T U : Type} {N : Usize} (cmp : core.cmp.PartialEq T U)
    (bytes : Slice T) (array : Array U N) : Result Bool :=
  core.slice.cmp.PartialEqSlice.eq cmp bytes (Array.to_slice array)

/-- Complete actual helper installation. No SDK-read interpretations remain:
account metadata, alias slots, borrow operations, snapshots, release and writes
are the emitted reference body. Only digest/error syscall interpretation and
current verifier children remain at this boundary. -/
def install (ops : SdkReference.Ops) (verifierOps : AspisR1CurrentCaller.Ops) : SdkReference.Ops :=
  {ops with
    op0:=@SourceInstallation.stdSliceArrayNe,
    op1:=@stdSliceArrayEq,
    op2:=@SourceInstallation.stdOption,
    op3:=@SourceInstallation.currentChild verifierOps,
    op4:=ok 57607#usize,
    op5:=SourceInstallation.actualValidator,
    op6:=SourceInstallation.actualDecoder,
    op7:=ok 688#usize,
    op8:=SourceInstallation.actualEncoder,
    op9:=fun _ => ok ()}

/-- Audit of the actual remaining owned caller fields, rather than an Ops
record concealing discarded decoder/SDK read assumptions. -/
theorem install_dependencies (ops other : SdkReference.Ops)
    (verifierOps : AspisR1CurrentCaller.Ops)
    (hd : ops.op10=other.op10) (he : ops.op11=other.op11) :
    install ops verifierOps=install other verifierOps := by
  cases ops
  cases other
  cases hd
  cases he
  rfl

/-- Helper-only compatibility with the already checked decoder/first body.
The two SDK IO fields are unreachable in these helpers and deliberately div.
This is not a substitution for the complete SDK-state parent. -/
def legacyHelperOps (ops : SdkReference.Ops) : AspisS2OwnedStage1.Ops where
  op0:=@ops.op0
  op1:=@ops.op2
  op2:=@ops.op3
  op3:=ops.op4
  op4:=ops.op5
  op5:=ops.op6
  op6:=ops.op7
  op7:=ops.op8
  op8:=ops.op9
  op9:=ops.op10
  op10:=ops.op11
  op11:=div
  op12:=div

theorem boxed_eq (ops : SdkReference.Ops) (bytes : Slice U8) :
    SdkReference.decode_public_statement_box ops bytes =
      AspisS2OwnedStage1.decode_public_statement_box (legacyHelperOps ops) bytes := rfl

theorem first_eq (ops : SdkReference.Ops) (pub : Reachability.Public)
    (bytes proof : Slice U8) (k : Usize) :
    SdkReference.first_decoded ops pub bytes proof k =
      AspisS2OwnedStage1.first_decoded (legacyHelperOps ops) pub bytes proof k := rfl

theorem observer_none : SdkReference.observer = ok none := rfl

private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let a ← m; f a)=ok out) : ∃ a,m=ok a ∧ f a=ok out := by
  cases m with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem first_success (ops : SdkReference.Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (pub : Reachability.Public) (bytes proof : Slice U8) (k : Usize) (cp : alloc.vec.Vec U8)
    (h : SdkReference.first_decoded (install ops verifierOps) pub bytes proof k=ok (.Ok cp)) :
    AspisR1CurrentCaller.verifier.candidate.tx1 verifierOps
      (SourceInstallation.currentDigest
        (SdkReference.SolanaDigest.Insts.Aspis_coreDigestDigest32 (install ops verifierOps)))
      (CurrentCarrier.toCurrentPublic pub) bytes proof k () none=ok (.Ok cp) := by
  unfold SdkReference.first_decoded at h
  rw [observer_none] at h
  simp only [bind_tc_ok] at h
  obtain ⟨r,hr,h⟩ := bind_success _ _ _ h
  cases r with
  | Err error =>
    change (do let mapped ← ops.op11 error; ok (core.result.Result.Err mapped)) = ok (.Ok cp) at h
    obtain ⟨_,_,h⟩ := bind_success _ _ _ h
    cases h
  | Ok value =>
    simp only [SdkReference.core.result.Result.map_err] at h
    cases h
    exact SourceInstallation.child_success verifierOps _ pub bytes proof k () cp hr

#print axioms install_dependencies
#print axioms boxed_eq
#print axioms first_eq
#print axioms observer_none
#print axioms first_success
end AspisS2OwnedStage1.SdkReference.Installation
