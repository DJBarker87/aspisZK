import NDO_JFo_Header
import NDO_JFo_Tail
import NDO_JFo_RangeEnds
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFo_Resume
open Aeneas Aeneas.Std Result AspisR1Stage2

/-- The three actual hash calls are explicit boundaries. This is a forward
reader theorem, not a computed SHA256 theorem or accepted-wrapper result. -/
theorem source {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (proofHash : D.digest hash (Array.to_slice (Array.make 1#usize [JFx_NativeBytes.proof]))=
      ok JFo_AuthBytes.proofHash)
    (publicHash : D.digest hash (Array.to_slice (Array.make 1#usize [JFx_NativeBytes.publicInput]))=
      ok JFo_AuthBytes.publicHash)
    (checksumHash : D.digest hash (Array.to_slice (Array.make 2#usize
      [Array.to_slice (Array.make 22#usize
        [85#u8,78#u8,80#u8,82#u8,79#u8,86#u8,69#u8,68#u8,58#u8,82#u8,49#u8,58#u8,
         99#u8,104#u8,101#u8,99#u8,107#u8,112#u8,111#u8,105#u8,110#u8,116#u8]),
       JFq_Range.segment 0 1736 (by decide)]))=ok JFo_AuthBytes.checksum) :
    Port4A_NativeReader.resume (CheckpointBytes4Ops.ops true) D JFx_NativeBytes.checkpoint
      JFx_NativeBytes.proof JFx_NativeBytes.publicInput .S2 hash=
        ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) := by
  rw [← T2Nat_ResumePrefix.source]
  have size : Slice.len JFx_NativeBytes.checkpoint=1768#usize := by
    apply UScalar.eq_of_val_eq
    exact JFx_NativeBytes.checkpointBytes_length
  have proofRead:=JFq_Range.read 16#usize 48#usize (by decide) (by decide)
  have publicRead:=JFq_Range.read 48#usize 80#usize (by decide) (by decide)
  have magic := JFo_Header.magic
  dsimp only [JFo_AuthBytes.magic] at magic
  have neProof:=JFq_Compare.ne _ _ JFo_AuthBytes.proofHash_selected
  have nePublic:=JFq_Compare.ne _ _ JFo_AuthBytes.publicHash_selected
  have suffix := JFo_RangeEnds.suffix
  have selectedPrefix := JFo_RangeEnds.leading
  have endeq : Usize.wrapping_sub 1768#usize 32#usize=1736#usize := by
    apply UScalar.eq_of_val_eq
    rw [Usize.wrapping_sub_val_eq]
    have cap : 1768 < UScalar.size .Usize := by rw [UScalar.size_def];scalar_tac
    change (1768+(UScalar.size .Usize-32))%UScalar.size .Usize=1736
    rw [show 1768+(UScalar.size .Usize-32)=1736+UScalar.size .Usize by omega,
      Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
  have nextBound : ¬(10#u8 > 22#u8) := by decide
  simp only [T2Nat_ResumePrefix.body,CheckpointBytes4Ops.ops,size,T2Nat_ReaderNonvacuity.size_s2,
    bne_self_eq_false,Bool.false_eq_true,ite_false,JFo_AuthBytes.prefix_read,
    core.cmp.impls.PartialEqShared.ne,slicePartialEq,magic,JFo_Header.tag,
    CheckpointBytes4Ops.tag,JFo_Header.cursor,JFo_Header.version,
    JFo_Header.reserved,JFo_Header.iterator,JFo_Header.scanned,
    show (16#usize).val=16 from rfl,show (48#usize).val=48 from rfl,
    show (80#usize).val=80 from rfl,Nat.reduceSub,
    proofRead,publicRead,proofHash,publicHash,neProof,nePublic,suffix,selectedPrefix,checksumHash,endeq,nextBound,
    bind_tc_ok,Aeneas.Std.uncurry,lift]
  exact JFo_Tail.source

#print axioms source
end AspisR1.JFo_Resume
end
