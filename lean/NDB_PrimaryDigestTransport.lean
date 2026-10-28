import NDB_PrimaryDigestRun
import NCV_ArrayRead
import JFt_DigestInjective
set_option autoImplicit false
namespace NDB_PrimaryDigestTransport
open Aeneas Aeneas.Std Result AspisR1

theorem chunk (target : Array U32 8#usize) (k : Nat) (bound : k<8) :
    ((AspisS6SourceCodec.DigestContents.chunks target).drop (4*k)).take 4=
      (core.num.U32.to_le_bytes (NCV_ArrayFrame.coord target k)).val := by
  have h : k<target.val.length := by simpa only [target.property,show (8#usize).val=8 from rfl] using bound
  have coord : NCV_ArrayFrame.coord target k=target.val[k] := by
    simp only [NCV_ArrayFrame.coord,List.getElem?_eq_getElem h,Option.getD_some]
  rw [coord]
  interval_cases k <;>
    simp [AspisS6SourceCodec.DigestContents.chunks,JFt_DigestInjective.word_length,
      List.drop_append,List.take_append]

theorem subwindow (xs : List U8) (s k : Nat) (bound : k<8) :
    (xs.drop (s+4*k)).take 4=(((xs.drop s).take 32).drop (4*k)).take 4 := by
  simp only [List.drop_take,List.drop_drop,List.take_take]
  have h : 4 ≤ 32-4*k := by omega
  simp only [Nat.min_eq_left h]

theorem value (b : Slice U8) (s : Usize) (target : Array U32 8#usize)
    (cap : b.val.length ≤ 768) (fit : s.val+32 ≤ b.val.length)
    (contents : AspisS6SourceCodec.DigestContents.chunks target=(b.val.drop s.val).take 32)
    (canonical : JFu_DigestCanonical.Canonical target) :
    NCV_Reference.digest b s=ok (.Ok target) := by
  apply NDB_PrimaryDigestRun.value b s target
    (fun k=>core.num.U32.to_le_bytes (NCV_ArrayFrame.coord target k)) cap fit
  · intro k hk
    rw [subwindow b.val s.val k hk,←contents]
    exact chunk target k hk
  · intro k hk
    exact JFt_DigestInjective.from_to _
  · intro k hk
    rw [JFt_DigestInjective.from_to]
    have h : k<target.val.length := by simpa only [target.property,show (8#usize).val=8 from rfl] using hk
    simpa only [NCV_ArrayFrame.coord,List.getElem?_eq_getElem h,Option.getD_some] using canonical ⟨k,hk⟩

theorem source (b : Slice U8) (s : Usize) (target : Array U32 8#usize)
    (cap : b.val.length ≤ 768) (fit : s.val+32 ≤ b.val.length)
    (call : AspisS6NativeSnapshotReadDigest.read_digest
      (JHg_FieldRead.segment b s.val 32)=ok (.Ok target)) :
    NCV_Reference.digest b s=ok (.Ok target) := by
  have size : (JHg_FieldRead.segment b s.val 32).length=32 := JHg_FieldRead.length b s.val 32 fit
  have canonical:=JFu_DigestSliceCanonical.source _ _ call
  obtain ⟨out,read,post⟩:=WP.spec_imp_exists
    (AspisS6NativeSnapshotReadDigest.read_digest_spec (JHg_FieldRead.segment b s.val 32) size)
  have same : out=.Ok target := Result.ok.inj (read.symm.trans call)
  have contents:=post target same
  exact value b s target cap fit contents canonical

#print axioms chunk
#print axioms subwindow
#print axioms value
#print axioms source
end NDB_PrimaryDigestTransport
