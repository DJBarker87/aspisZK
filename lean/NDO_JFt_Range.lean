import NDO_JFu_PublicRange
import NDO_JFu_PublicWindowFacts
set_option autoImplicit false
namespace AspisR1.JFt_Range
open Aeneas Aeneas.Std Result WP

theorem read (off n : Nat) (bound : off+n≤1880) (start stop : Usize)
    (order : start.val≤stop.val) (inside : stop.val≤n) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      (JFu_PublicRange.segment off n bound) {start:=start,«end»:=stop}=
      ok (JFu_PublicRange.segment (off+start.val) (stop.val-start.val) (by omega)) := by
  have size:=JFu_PublicRange.length off n bound
  have spec : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      (JFu_PublicRange.segment off n bound) {start:=start,«end»:=stop}
      ⦃ out => out=JFu_PublicRange.segment (off+start.val) (stop.val-start.val) (by omega) ⦄ := by
    unfold core.slice.index.Slice.index
    step*
    all_goals apply Subtype.ext
    all_goals simpa only [List.slice,JFu_PublicRange.segment,
      JFu_PublicRange.nested _ off n start.val (stop.val-start.val) (by omega)] using out_post1
  obtain ⟨out,call,same⟩:=WP.spec_imp_exists spec
  rw [same] at call
  exact call

theorem digest (off : Nat) (member : off ∈ JFu_PublicDigests.offsets) (bound : off+32≤1880) :
    ∃ out,AspisS6NativeSnapshotReadDigest.read_digest (JFu_PublicRange.segment off 32 bound)=ok (.Ok out) ∧
      JFu_DigestCanonical.Canonical out ∧
      AspisS6SourceCodec.DigestContents.chunks out=(JFx_NativeBytes.publicInput.val.drop off).take 32 :=
  JFu_PublicWindowFacts.source off member _ rfl (JFu_PublicRange.length off 32 bound)

#print axioms read
#print axioms digest
end AspisR1.JFt_Range
