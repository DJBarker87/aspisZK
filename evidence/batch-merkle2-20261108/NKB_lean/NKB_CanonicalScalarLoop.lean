import NKB_CanonicalTail
set_option autoImplicit false
namespace NKB_CanonicalScalarLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR1 NKB_CanonicalRange
open NKB_CanonicalPair

def index (n : Nat) : Usize := UScalar.ofNat (n%32) (by scalar_tac)
def read (q : Slice U8) (s l : Usize) : Option (Array U8 4#usize) :=
 if h : (NKB_CanonicalScalar.window q s l).val.length=4 then
   some ⟨(NKB_CanonicalScalar.window q s l).val,h⟩ else none

def pass (f : Array U8 4#usize→Option U32) (q : Slice U8) (s : Usize) (n : Nat) : Bool :=
 ((read q s (index n)).bind f).isSome

theorem actual (f : Array U8 4#usize→Option U32) (q : Slice U8) (s l : Usize)
 (length : q.val.length=832) (slot : s.val<4) (lane : l.val<26) :
 pass f q s l.val=(f (⟨(NKB_CanonicalScalar.window q s l).val,
   NKB_CanonicalScalar.size q s l length slot lane⟩ : Array U8 4#usize)).isSome := by
 have eq : index l.val=l := by
   apply UScalar.eq_of_val_eq
   change l.val%32=l.val
   exact Nat.mod_eq_of_lt (by omega)
 simp only [pass,eq,read,dif_pos (NKB_CanonicalScalar.size q s l length slot lane),Option.bind_some]

/-- All 26 scalar iterations plus their K tail, retaining the complete
pending-return/continuation marker rather than a success-only scan fact. -/
theorem source (f : Array U8 4#usize→Option U32) (g : Slice U8→Option K)
 (q : Slice U8) (s : Usize) (length : q.val.length=832) (slot : s.val<4)
 (fuel : Nat) (iter : core.ops.range.Range Usize)
 (ending : iter.end=26#usize) (span : iter.start.val+fuel=26) :
 NJS_Extract.verifier.candidate.canonical_scan_loop0_loop0_loop0
   (fun b=>ok (f b)) (fun b=>ok (g b)) iter q s none=
 ok (if allFrom (pass f q s) iter.start.val fuel && NKB_CanonicalTail.accepted g q s
   then (none,1#u32) else (some (.Err .Parse : ScanResult),0#u32)) := by
 induction fuel generalizing iter with
 | zero=>
   have body:=NKB_CanonicalTail.source f g q s iter length slot (by rw [ending];change 26≤ iter.start.val;omega)
   unfold NJS_Extract.verifier.candidate.canonical_scan_loop0_loop0_loop0
   rw [Aeneas.Std.loop.eq_def,body]
   simp only [bind_tc_ok,allFrom,Bool.true_and]
 | succ fuel ih=>
   have lane : iter.start.val<26:=by omega
   obtain ⟨iter1,hs,he,body⟩:=NKB_CanonicalScalar.entered f g q s none iter length slot lane (by rw [ending];exact lane)
   have tail:=ih iter1 (he.trans ending) (by omega)
   let b : Array U8 4#usize:=⟨(NKB_CanonicalScalar.window q s iter.start).val,NKB_CanonicalScalar.size q s iter.start length slot lane⟩
   have same:=actual f q s iter.start length slot lane
   change pass f q s iter.start.val=(f b).isSome at same
   cases reply:f b with
   | none=>
     have bad : pass f q s iter.start.val=false:=by simpa only [reply,Option.isSome_none] using same
     dsimp only [b] at reply
     unfold NJS_Extract.verifier.candidate.canonical_scan_loop0_loop0_loop0
     rw [Aeneas.Std.loop.eq_def,body]
     simp [reply,allFrom,bad]
   | some value=>
     have good : pass f q s iter.start.val=true:=by simpa only [reply,Option.isSome_some] using same
     dsimp only [b] at reply
     unfold NJS_Extract.verifier.candidate.canonical_scan_loop0_loop0_loop0
     rw [Aeneas.Std.loop.eq_def,body]
     simpa only [NJS_Extract.verifier.candidate.canonical_scan_loop0_loop0_loop0,reply,bind_tc_ok,allFrom,good,Bool.true_and,hs] using tail

#print axioms actual
#print axioms source
end NKB_CanonicalScalarLoop
