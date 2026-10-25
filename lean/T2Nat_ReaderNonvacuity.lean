import T2Nat_ReaderJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_ReaderNonvacuity
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem size_s2 : CheckpointBytes4Ops.checkpointSize .S2 = ok 1768#usize := by
  unfold CheckpointBytes4Ops.checkpointSize CheckpointBytes4Ops.finalLen
  simp only [bind_tc_ok]
  rw [Port4A_ReaderInstall.mul_value _ _ (by decide),bind_tc_ok,
    Port4A_ReaderInstall.add_value _ _ (by decide)]
  rfl

def empty : Slice U8 := ⟨[],by simp⟩

/-- A reached native reader rejection with the actual caller's error carrier;
there is no reader-acceptance premise or assumed digest success. -/
theorem empty_rejects {H : Type} (D : VTop_Stages.aspis_core.digest.Digest32 H)
    (hash : H) (proof pub : Slice U8) :
    T2Nat_ReaderJoin.reader true D empty proof pub .S2 hash =
      ok (.Err (Port3_CheckpointInstall.error verifier.Error.Checkpoint)) := by
  have size : (T2Nat_ReaderOps.ops true).checkpointSize .S2 = ok 1768#usize := size_s2
  have reject : (Slice.len empty != 1768#usize) = true := by
    simp only [bne_iff_ne]
    intro same
    have values := congrArg UScalar.val same
    change 0 = 1768 at values
    omega
  simp only [T2Nat_ReaderJoin.reader,Port4A_NativeReader.resume,size,bind_tc_ok,
    reject,ite_true]

/-- Native raw-body admission is inhabited at EVERY in-bounds cursor, for
arbitrary actual byte contents; exact bytes and reader frame are constructed. -/
theorem raw_total (r : verifier.Reader) (N : Usize)
    (bound : r.at.val+N.val ≤ r.bytes.val.length) :
    ∃ b out, T2Nat_ScalarJoin.raw T2Nat_ReaderOps.unwrap N r = ok (b,out) ∧
      b.val = (r.bytes.val.drop r.at.val).take N.val ∧
      out.at.val = r.at.val+N.val ∧ out.bytes = r.bytes := by
  obtain ⟨b,out,run,contents,cursor,frame⟩ := OraclePortCkptAbi2Unwrap.raw_panic_unreachable
    r N (fun _ => fail .panic) bound
  refine ⟨b,out,?_,contents,cursor,frame⟩
  rw [T2Nat_ScalarJoin.raw,T2Nat_RawJoin.reference N T2Nat_ReaderOps.unwrap T2Nat_ReaderOps.unwrap_ok r bound]
  exact run

#print axioms size_s2
#print axioms empty_rejects
#print axioms raw_total
end AspisR1.T2Nat_ReaderNonvacuity
end
