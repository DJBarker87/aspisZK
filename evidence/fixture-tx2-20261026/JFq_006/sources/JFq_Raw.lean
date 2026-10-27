import JFx_NativeBytes
import T2Nat_ReaderNonvacuity
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFq_Raw
open Aeneas Aeneas.Std Result AspisR1Stage2

def reader (pos : Usize) : verifier.Reader := ⟨JFx_NativeBytes.checkpoint,pos⟩

theorem source (pos N : Usize) (b : Array U8 N)
    (bound : pos.val+N.val≤1768)
    (selected : (JFx_NativeBytes.checkpoint.val.drop pos.val).take N.val=b.val) :
    CheckpointBytes3Reader.raw N (reader pos)=
      ok (b,reader (Usize.wrapping_add pos N)) := by
  have size : JFx_NativeBytes.checkpoint.val.length=1768 := JFx_NativeBytes.checkpointBytes_length
  obtain ⟨out,last,run,bytes,cursor,frame⟩ :=
    OraclePortCkptAbi2Unwrap.raw_panic_unreachable (reader pos) N
      (fun _ => fail .panic) (by change pos.val+N.val≤JFx_NativeBytes.checkpoint.val.length;omega)
  have same : out=b := Subtype.ext (bytes.trans selected)
  have wrap : (Usize.wrapping_add pos N).val=pos.val+N.val := by
    rw [Usize.wrapping_add_val_eq,Nat.mod_eq_of_lt]
    have less : pos.val+N.val < UScalar.size .Usize := by
      have cur : last.at.val=pos.val+N.val := cursor
      rw [← cur]
      exact last.at.hBounds
    exact less
  have lastEq : last=reader (Usize.wrapping_add pos N) := by
    cases last
    simp only [reader,verifier.Reader.mk.injEq] at *
    exact ⟨frame,UScalar.eq_of_val_eq (cursor.trans wrap.symm)⟩
  change verifier.Reader.rawWithUnwrap N _ _ = _
  rw [run,same,lastEq]

#print axioms source
end AspisR1.JFq_Raw
end
