import NKB_CanonicalRange
set_option autoImplicit false
namespace NKB_CanonicalPair
open Aeneas Aeneas.Std Result ControlFlow AspisR1 NKB_CanonicalRange

def allFrom (pass : Nat→Bool) : Nat→Nat→Bool
 | _,0=>true
 | start,fuel+1=>pass start && allFrom pass (start+1) fuel

/-- Induction over the actual source Range state, with arbitrary pending
return and both decoder outcomes. Native local reads are K027/K028; these
parameters describe only child Option replies, never a parent result. -/
theorem loop (f : Slice U8→Option K) (q : Slice U8) (s : Usize)
 (size : q.val.length=832) (slot : s.val<4) (pass : Nat→Bool)
 (cuts : ∀ l : Usize,l.val<2 → (f (window q s l)).isSome=pass l.val)
 (fuel : Nat) (iter : core.ops.range.Range Usize) (p : Pending)
 (ending : iter.end=2#usize) (span : iter.start.val+fuel=2) :
 NJS_Extract.verifier.candidate.canonical_scan_loop0_loop0_loop0_loop0
   (fun bs=>ok (f bs)) iter q s p=
 ok (if allFrom pass iter.start.val fuel then p else some (.Err .Parse)) := by
 induction fuel generalizing iter with
 | zero=>
   obtain ⟨iter1,run⟩:=NKB_CanonicalRange.stop iter (by rw [ending];change 2≤ iter.start.val;omega)
   unfold NJS_Extract.verifier.candidate.canonical_scan_loop0_loop0_loop0_loop0
   rw [Aeneas.Std.loop.eq_def]
   simp [NJS_Extract.verifier.candidate.canonical_scan_loop0_loop0_loop0_loop0.body,
     run,allFrom]
 | succ fuel ih=>
   have lane : iter.start.val<2 := by omega
   obtain ⟨iter1,hs,he,body⟩:=entered f q s p iter size slot lane (by rw [ending];exact lane)
   have tail:=ih iter1 (he.trans ending) (by omega)
   have cut:=cuts iter.start lane
   cases reply:f (window q s iter.start) with
   | none=>
     have bad : pass iter.start.val=false := by simpa only [reply,Option.isSome_none] using cut.symm
     unfold NJS_Extract.verifier.candidate.canonical_scan_loop0_loop0_loop0_loop0
     rw [Aeneas.Std.loop.eq_def,body]
     simp [reply,allFrom,bad]
   | some value=>
     have good : pass iter.start.val=true := by simpa only [reply,Option.isSome_some] using cut.symm
     unfold NJS_Extract.verifier.candidate.canonical_scan_loop0_loop0_loop0_loop0
     rw [Aeneas.Std.loop.eq_def,body]
     simpa only [NJS_Extract.verifier.candidate.canonical_scan_loop0_loop0_loop0_loop0,reply,bind_tc_ok,allFrom,good,Bool.true_and,hs] using tail

/-- Both actual K2 reads, not a caller-supplied verdict sequence. -/
theorem source (f : Slice U8→Option K) (q : Slice U8) (s : Usize)
 (size : q.val.length=832) (slot : s.val<4) (p : Pending) :
 NJS_Extract.verifier.candidate.canonical_scan_loop0_loop0_loop0_loop0
   (fun bs=>ok (f bs)) {start:=0#usize,«end»:=2#usize} q s p=
 ok (if (f (window q s 0#usize)).isSome && (f (window q s 1#usize)).isSome
   then p else some (.Err .Parse)) := by
 let pass : Nat→Bool:=fun n=>if n=0 then (f (window q s 0#usize)).isSome
   else (f (window q s 1#usize)).isSome
 have cuts : ∀ l : Usize,l.val<2→(f (window q s l)).isSome=pass l.val := by
   intro l small
   by_cases zero : l.val=0
   · have eq : l=0#usize:=UScalar.eq_of_val_eq zero
     simp [pass,zero,eq]
   · have one : l.val=1:=by omega
     have eq : l=1#usize:=UScalar.eq_of_val_eq one
     simp [pass,one,eq]
 have total:=loop f q s size slot pass cuts 2 {start:=0#usize,«end»:=2#usize} p rfl (by rfl)
 simpa only [allFrom,pass,show (0#usize).val=0 from rfl,Nat.zero_add,
   if_pos rfl,show ¬(1:Nat)=0 by decide,if_false,Bool.and_true] using total

#print axioms source

#print axioms loop
end NKB_CanonicalPair
