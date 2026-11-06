import NKB_CanonicalOpening
set_option autoImplicit false
namespace NKB_CanonicalSlotLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR1 NKB_CanonicalRange NKB_CanonicalPair
open NKB_CanonicalOpening

def pass (f : Array U8 4#usize→Option U32) (g : Slice U8→Option K) (q : Slice U8) (n : Nat) : Bool :=
 slot f g q (NKB_CanonicalScalarLoop.index n)

theorem actual (f : Array U8 4#usize→Option U32) (g : Slice U8→Option K) (q : Slice U8)
 (s : Usize) (bound : s.val<4) : pass f g q s.val=slot f g q s := by
 have same : NKB_CanonicalScalarLoop.index s.val=s := by
   apply UScalar.eq_of_val_eq
   change s.val%32=s.val
   exact Nat.mod_eq_of_lt (by omega)
 simp only [pass,same]

/-- Four source s-iterations then the final echeck; each continuation keeps
pending=none, and each rejection terminates with Err(Parse), marker zero. -/
theorem source (f : Array U8 4#usize→Option U32) (g : Slice U8→Option K)
 (ec : Slice U8→Bool) (q : Slice U8) (length : q.val.length=832)
 (fuel : Nat) (iter : core.ops.range.Range Usize)
 (ending : iter.end=4#usize) (span : iter.start.val+fuel=4) :
 NJS_Extract.verifier.candidate.canonical_scan_loop0_loop0
   (fun b=>ok (f b)) (fun b=>ok (g b)) (fun b _=>ok (reply (ec b))) iter q none=
 ok (if allFrom (pass f g q) iter.start.val fuel && ec (trailing q)
 then (none,1#u32) else (some (.Err .Parse),0#u32)) := by
 induction fuel generalizing iter with
 | zero=>
   have body:=NKB_CanonicalOpening.stop f g ec q length iter (by rw [ending];change 4≤ iter.start.val;omega)
   unfold NJS_Extract.verifier.candidate.canonical_scan_loop0_loop0
   conv_lhs=>unfold Aeneas.Std.loop
   simp [body,allFrom]
 | succ fuel ih=>
   have bound : iter.start.val<4:=by omega
   obtain ⟨iter1,hs,he,body⟩:=NKB_CanonicalOpening.entered f g ec q length iter (by rw [ending];exact bound) bound
   have tail:=ih iter1 (he.trans ending) (by omega)
   have same:=actual f g q iter.start bound
   cases verdict:slot f g q iter.start with
   | false=>
     have bad : pass f g q iter.start.val=false:=same.trans verdict
     unfold NJS_Extract.verifier.candidate.canonical_scan_loop0_loop0
     conv_lhs=>unfold Aeneas.Std.loop
     simp [body,verdict,allFrom,bad]
   | true=>
     have good : pass f g q iter.start.val=true:=same.trans verdict
     unfold NJS_Extract.verifier.candidate.canonical_scan_loop0_loop0
     conv_lhs=>unfold Aeneas.Std.loop
     simpa [NJS_Extract.verifier.candidate.canonical_scan_loop0_loop0,
       body,verdict,allFrom,good,hs] using tail

#print axioms actual
#print axioms source
end NKB_CanonicalSlotLoop
