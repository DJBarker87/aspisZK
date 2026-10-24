import VTop_Checkpoint

/-! Concrete checkpoint REFERENCE installation. The selector writer is S2
specific. Native source adoption is the domain-sensitive P6 obligation; no
native equality or successful observation is a field of this construction. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_CheckpointInstall
open Aeneas Aeneas.Std Result VTop_Stages
open CheckpointBytes5Effect

/-- Converse of erasure, for the SAME Code execution and any initial log. -/
theorem erase_success_run {A H : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H)
    (code : Code A) (a : A) (accepted : erase D hash code = ok a) (before : Log) :
    ∃ after, run D hash code before = ok (a,after) := by
  induction code generalizing before with
  | done value =>
    have eq := Result.ok.inj accepted
    subst value
    exact ⟨before,rfl⟩
  | step r k ih =>
    cases r with
    | fail e => cases accepted
    | div => cases accepted
    | ok b => exact ih b accepted before
  | read parts k ih =>
    cases call : D.digest hash parts with
    | fail e => simp only [erase,call,bind_tc_fail] at accepted; cases accepted
    | div => simp only [erase,call,bind_tc_div] at accepted; cases accepted
    | ok b =>
      simp only [erase,call,bind_tc_ok] at accepted
      obtain ⟨after,success⟩ := ih b accepted (before ++ [(parts,b)])
      exact ⟨after,by simpa only [run,call,bind_tc_ok] using success⟩

def writer {H : Type} (D : aspis_core.digest.Digest32 H)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (proof pub : Slice U8) (hash : H) : Result (alloc.vec.Vec U8) := do
  let ck ← erase (VTop_Checkpoint.digest D) hash
    (CheckpointBytes5Writer.writer (CheckpointBytes3Namespaces.toPrepared p)
      (CheckpointBytes3Namespaces.toAccumulator a) proof pub)
  ok ⟨ck.val,ck.property⟩

def error : AspisR1Stage2.verifier.Error → verifier.Error
  | .Parse => .Parse | .Semantic => .Semantic | .Transcript => .Transcript
  | .Relation => .Relation | .Merkle => .Merkle | .Query => .Query
  | .Checkpoint => .Checkpoint | .Allocation => .Allocation

def reader (reserved : Bool) {H : Type} (D : aspis_core.digest.Digest32 H)
    (ck proof pub : Slice U8) (v : transport.Variant) (hash : H) :
    Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
  let out ← AspisR1Stage2.verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved)
    (VTop_Checkpoint.digest D) ck proof pub v hash
  match out with
  | .Ok pair => ok (.Ok pair)
  | .Err e => ok (.Err (error e))

/-- Remaining operations are visibly unchanged and uninstalled. -/
def install (base : Ops) (reserved : Bool) : Ops :=
  {base with op8 := writer, op18 := reader reserved}

theorem writer_run {H : Type} (D : aspis_core.digest.Digest32 H)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (proof pub : Slice U8) (hash : H) (saved : alloc.vec.Vec U8)
    (accepted : writer D p a proof pub hash = ok saved) (before : Log) :
    ∃ after, run (VTop_Checkpoint.digest D) hash
      (CheckpointBytes5Writer.writer (CheckpointBytes3Namespaces.toPrepared p)
        (CheckpointBytes3Namespaces.toAccumulator a) proof pub) before =
        ok (VTop_Checkpoint.checkpointSlice saved,after) := by
  unfold writer at accepted
  generalize h : erase (VTop_Checkpoint.digest D) hash
    (CheckpointBytes5Writer.writer (CheckpointBytes3Namespaces.toPrepared p)
      (CheckpointBytes3Namespaces.toAccumulator a) proof pub) = result at accepted
  cases result with
  | fail e => cases accepted
  | div => cases accepted
  | ok ck =>
    have eq := Result.ok.inj accepted
    subst saved
    exact erase_success_run _ _ _ ck h before

theorem reader_success (reserved : Bool) {H : Type} (D : aspis_core.digest.Digest32 H)
    (ck proof pub : Slice U8) (v : transport.Variant) (hash : H)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (accepted : reader reserved D ck proof pub v hash = ok (.Ok (p,a))) :
    AspisR1Stage2.verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved)
      (VTop_Checkpoint.digest D) ck proof pub v hash = ok (.Ok (p,a)) := by
  unfold reader at accepted
  generalize h : AspisR1Stage2.verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved)
    (VTop_Checkpoint.digest D) ck proof pub v hash = result at accepted
  cases result with
  | fail e => cases accepted
  | div => cases accepted
  | ok r =>
    cases r with
    | Err e => cases accepted
    | Ok pair =>
      have eq := core.result.Result.Ok.inj (Result.ok.inj accepted)
      subst pair
      rfl

/-- Discharges the entire CheckpointSourceJoin for the reference installation.
State provenance and actual Rust-to-reference adoption remain separate. -/
theorem source_join (base : Ops) (reserved : Bool) {H : Type}
    (D : aspis_core.digest.Digest32 H) (hash : H) :
    VTop_Checkpoint.CheckpointSourceJoin (install base reserved) D hash reserved := by
  constructor
  · intro semantic proof pub split p a saved _ accepted
    obtain ⟨after,success⟩ := writer_run D p a proof pub hash saved accepted []
    exact ⟨[],after,success⟩
  · intro ck proof pub p a accepted
    exact reader_success reserved D ck proof pub .S2 hash p a accepted

#print axioms erase_success_run
#print axioms writer_run
#print axioms reader_success
#print axioms source_join
end AspisR1.Port3_CheckpointInstall
end
