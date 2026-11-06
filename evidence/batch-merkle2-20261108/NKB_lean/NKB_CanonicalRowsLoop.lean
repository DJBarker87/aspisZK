import NKB_CanonicalRows
set_option autoImplicit false
namespace NKB_CanonicalRowsLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR1 NKB_CanonicalRange NKB_CanonicalPair NKB_CanonicalOpening

/-- Source-only finite chain: all 22 openings, first Parse rejection, and
successful exhaustion producing Some(Ok), so the top-level None/panic arm is
unreachable for these total child interpretations. Not a CLOSED row root. -/
theorem source (f : Array U8 4#usize→Option U32) (g : Slice U8→Option K)
 (ec : Slice U8→Bool) (proof : Slice U8) (length : proof.val.length=57607)
 (fuel : Nat) (iter : core.ops.range.Range Usize)
 (ending : iter.end=22#usize) (span : iter.start.val+fuel=22) :
 NJS_Extract.verifier.candidate.canonical_scan_loop0
   (fun b=>ok (f b)) (fun b=>ok (g b)) (fun b _=>ok (reply (ec b))) iter proof none=
 ok (some (reply (allFrom (NKB_CanonicalRows.pass f g ec proof) iter.start.val fuel))) := by
 induction fuel generalizing iter with
 | zero=>
   obtain ⟨iter1,run⟩:=NKB_CanonicalRange.stop iter (by rw [ending];change 22≤ iter.start.val;omega)
   have body : NJS_Extract.verifier.candidate.canonical_scan_loop0.body
     (fun b=>ok (f b)) (fun b=>ok (g b)) (fun b _=>ok (reply (ec b))) proof iter none=
     ok (done (some (.Ok ()))) := by
     simp [NJS_Extract.verifier.candidate.canonical_scan_loop0.body,run]
   simp only [reply] at body
   unfold NJS_Extract.verifier.candidate.canonical_scan_loop0
   conv_lhs=>unfold Aeneas.Std.loop
   simp [body,allFrom,reply]
 | succ fuel ih=>
   have bound : iter.start.val<22:=by omega
   obtain ⟨iter1,hs,he,body⟩:=NKB_CanonicalRows.entered f g ec proof length iter (by rw [ending];exact bound) bound
   have tail:=ih iter1 (he.trans ending) (by omega)
   have same:=NKB_CanonicalRows.actual f g ec proof iter.start bound
   cases verdict:NKB_CanonicalRows.accepted f g ec proof iter.start with
   | false=>
     have bad : NKB_CanonicalRows.pass f g ec proof iter.start.val=false:=same.trans verdict
     simp only [reply] at body
     unfold NJS_Extract.verifier.candidate.canonical_scan_loop0
     conv_lhs=>unfold Aeneas.Std.loop
     simp [body,verdict,allFrom,bad,reply]
   | true=>
     have good : NKB_CanonicalRows.pass f g ec proof iter.start.val=true:=same.trans verdict
     simp only [reply] at body
     unfold NJS_Extract.verifier.candidate.canonical_scan_loop0
     conv_lhs=>unfold Aeneas.Std.loop
     simpa [NJS_Extract.verifier.candidate.canonical_scan_loop0,body,verdict,allFrom,good,hs,reply] using tail

#print axioms source
end NKB_CanonicalRowsLoop
