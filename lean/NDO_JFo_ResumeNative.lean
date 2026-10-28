import NDO_JFo_Resume
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFo_ResumeNative
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem source {H : Type} (D : VTop_Stages.aspis_core.digest.Digest32 H) (hash : H)
    (proofHash : D.digest hash (Array.to_slice (Array.make 1#usize [JFx_NativeBytes.proof]))=
      ok JFo_AuthBytes.proofHash)
    (publicHash : D.digest hash (Array.to_slice (Array.make 1#usize [JFx_NativeBytes.publicInput]))=
      ok JFo_AuthBytes.publicHash)
    (checksumHash : D.digest hash (Array.to_slice (Array.make 2#usize
      [Array.to_slice (Array.make 22#usize
        [85#u8,78#u8,80#u8,82#u8,79#u8,86#u8,69#u8,68#u8,58#u8,82#u8,49#u8,58#u8,
         99#u8,104#u8,101#u8,99#u8,107#u8,112#u8,111#u8,105#u8,110#u8,116#u8]),
       JFq_Range.segment 0 1736 (by decide)]))=ok JFo_AuthBytes.checksum) :
    T2Nat_ReaderJoin.reader true D JFx_NativeBytes.checkpoint JFx_NativeBytes.proof
      JFx_NativeBytes.publicInput .S2 hash=ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) ∧
    Port4A_ReaderInstall.reader true D JFx_NativeBytes.checkpoint JFx_NativeBytes.proof
      JFx_NativeBytes.publicInput .S2 hash=ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) := by
  have reference := JFo_Resume.source (VTop_Checkpoint.digest D) hash proofHash publicHash checksumHash
  have native := (T2Nat_ReaderJoin.resume true (VTop_Checkpoint.digest D) JFx_NativeBytes.checkpoint
    JFx_NativeBytes.proof JFx_NativeBytes.publicInput .S2 hash _).mpr reference
  constructor
  · simp only [T2Nat_ReaderJoin.reader,native,bind_tc_ok]
  · simp only [Port4A_ReaderInstall.reader,reference,bind_tc_ok]

#print axioms source
end AspisR1.JFo_ResumeNative
end
