import NKB_CanonicalSlotLoop
import Port4B_Opening
import R22Stage2LeafTotal
set_option autoImplicit false
namespace NKB_CanonicalRows
open Aeneas Aeneas.Std Result ControlFlow AspisR1 NKB_CanonicalRange NKB_CanonicalPair
open NKB_CanonicalOpening

theorem opening (proof : Slice U8) (i : Usize) :
 NJS_Extract.verifier.candidate.opening proof i=Port4B_Opening.opening proof i := by
 have width : NJS_Extract.compact.OPENING=ok 832#usize:=by
   simpa only [NJS_Extract.compact.OPENING,AspisR1Stage2.compact.OPENING] using AspisR1Stage2.r22_compact_OPENING_total
 have base : NJS_Extract.compact.OFF_OPENINGS=ok 10055#usize:=by
   simpa only [NJS_Extract.compact.OFF_OPENINGS,NJS_Extract.compact.FINAL_LEN,NJS_Extract.compact.OFF_FINAL,NJS_Extract.compact.OFF_ROUND1,NJS_Extract.compact.OFF_FOLDED_ROOT,NJS_Extract.compact.OFF_ROUND0,NJS_Extract.compact.OFF_INACTIVE,NJS_Extract.compact.COMPACT_Y1,NJS_Extract.compact.OFF_Y1,NJS_Extract.compact.COMPACT_SEMANTIC,NJS_Extract.compact.SEMANTIC_COMPACT_VALUES,NJS_Extract.compact.LOGICAL_SEMANTIC,NJS_Extract.compact.OFF_SEMANTIC,NJS_Extract.compact.HEADER,NJS_Extract.verifier.SEMANTIC_BYTES,AspisR1Stage2.compact.OFF_OPENINGS,AspisR1Stage2.compact.FINAL_LEN,AspisR1Stage2.compact.OFF_FINAL,AspisR1Stage2.compact.OFF_ROUND1,AspisR1Stage2.compact.OFF_FOLDED_ROOT,AspisR1Stage2.compact.OFF_ROUND0,AspisR1Stage2.compact.OFF_INACTIVE,AspisR1Stage2.compact.COMPACT_Y1,AspisR1Stage2.compact.OFF_Y1,AspisR1Stage2.compact.COMPACT_SEMANTIC,AspisR1Stage2.compact.SEMANTIC_COMPACT_VALUES,AspisR1Stage2.compact.LOGICAL_SEMANTIC,AspisR1Stage2.compact.OFF_SEMANTIC,AspisR1Stage2.compact.HEADER,AspisR1Stage2.verifier.SEMANTIC_BYTES] using AspisR1Stage2.r22_compact_OFF_OPENINGS_total
 simp only [NJS_Extract.verifier.candidate.opening,width,base,bind_tc_ok,Port4B_Opening.opening]

def accepted (f : Array U8 4#usize→Option U32) (g : Slice U8→Option K)
 (ec : Slice U8→Bool) (proof : Slice U8) (i : Usize) : Bool :=
 match NJS_Extract.verifier.candidate.opening proof i with
 | .ok q=>allFrom (NKB_CanonicalSlotLoop.pass f g q) 0 4 && ec (trailing q)
 | _=>false

def pass (f : Array U8 4#usize→Option U32) (g : Slice U8→Option K)
 (ec : Slice U8→Bool) (proof : Slice U8) (n : Nat) : Bool :=
 accepted f g ec proof (NKB_CanonicalScalarLoop.index n)

theorem actual (f : Array U8 4#usize→Option U32) (g : Slice U8→Option K)
 (ec : Slice U8→Bool) (proof : Slice U8) (i : Usize) (bound : i.val<22) :
 pass f g ec proof i.val=accepted f g ec proof i := by
 have same : NKB_CanonicalScalarLoop.index i.val=i:=by
   apply UScalar.eq_of_val_eq
   change i.val%32=i.val
   exact Nat.mod_eq_of_lt (by omega)
 simp only [pass,same]

/-- One actual opening iteration with its view and nested scanner fully
substituted. All 22 opening positions retain their own bounds and bytes. -/
theorem entered (f : Array U8 4#usize→Option U32) (g : Slice U8→Option K)
 (ec : Slice U8→Bool) (proof : Slice U8) (length : proof.val.length=57607)
 (iter : core.ops.range.Range Usize) (active : iter.start.val < iter.end.val)
 (bound : iter.start.val<22) :
 ∃ iter1,iter1.start.val=iter.start.val+1 ∧ iter1.end=iter.end ∧
 NJS_Extract.verifier.candidate.canonical_scan_loop0.body
   (fun b=>ok (f b)) (fun b=>ok (g b)) (fun b _=>ok (reply (ec b))) proof iter none=
 ok (if accepted f g ec proof iter.start then cont (iter1,none) else done (some (.Err .Parse))) := by
 obtain ⟨iter1,run,hs,he⟩:=NKB_CanonicalRange.next iter active
 obtain ⟨q,read,len,_⟩:=Port4B_Opening.opening_exact proof length iter.start bound
 rw [←opening] at read
 have child:=NKB_CanonicalSlotLoop.source f g ec q len 4 {start:=0#usize,«end»:=4#usize} rfl (by rfl)
 refine ⟨iter1,hs,he,?_⟩
 have same : accepted f g ec proof iter.start=(allFrom (NKB_CanonicalSlotLoop.pass f g q) 0 4 && ec (trailing q)) := by
   simp only [accepted,read]
 simp only [NJS_Extract.verifier.candidate.canonical_scan_loop0.body,run,bind_tc_ok]
 change (do
   let q←NJS_Extract.verifier.candidate.opening proof iter.start
   let (p,i)←NJS_Extract.verifier.candidate.canonical_scan_loop0_loop0
     (fun b=>ok (f b)) (fun b=>ok (g b)) (fun b _=>ok (reply (ec b))) {start:=0#usize,«end»:=4#usize} q none
   match i with
   | 1#uscalar=>ok (cont (iter1,p))
   | _=>match p with | none=>ok (done none) | some _=>ok (done p))=_
 rw [read]
 simp only [bind_tc_ok]
 rw [child,same]
 cases h:allFrom (NKB_CanonicalSlotLoop.pass f g q) 0 4 && ec (trailing q) <;>
   simp only [show (0#usize).val=0 from rfl,h,if_true,if_false] <;> rfl

#print axioms opening
#print axioms actual
#print axioms entered
end NKB_CanonicalRows
