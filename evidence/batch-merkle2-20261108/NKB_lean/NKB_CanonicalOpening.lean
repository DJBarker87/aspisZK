import NKB_CanonicalScalarLoop
set_option autoImplicit false
namespace NKB_CanonicalOpening
open Aeneas Aeneas.Std Result ControlFlow AspisR1 NKB_CanonicalRange NKB_CanonicalPair

def slot (f : Array U8 4#usize→Option U32) (g : Slice U8→Option K) (q : Slice U8) (s : Usize) : Bool :=
 allFrom (NKB_CanonicalScalarLoop.pass f q s) 0 26 && NKB_CanonicalTail.accepted g q s

def trailing (q : Slice U8) := MultiproofConeSlices.sub q 672#usize 800#usize

def reply (b : Bool) : ScanResult := if b then .Ok () else .Err .Parse

/-- The stopped s-range invokes exactly the final 128 bytes and propagates
its complete Result. This is a source-frame theorem, not a native call log. -/
theorem stop (f : Array U8 4#usize→Option U32) (g : Slice U8→Option K)
 (ec : Slice U8→Bool) (q : Slice U8) (length : q.val.length=832)
 (iter : core.ops.range.Range Usize) (ended : iter.end.val ≤ iter.start.val) :
 NJS_Extract.verifier.candidate.canonical_scan_loop0_loop0.body
   (fun b=>ok (f b)) (fun b=>ok (g b)) (fun b _=>ok (reply (ec b))) q iter none=
 ok (done (if ec (trailing q) then (none,1#u32) else (some (.Err .Parse : ScanResult),0#u32))) := by
 obtain ⟨iter1,run⟩:=NKB_CanonicalRange.stop iter ended
 have sliced:=MultiproofConeSlices.range_total q 672#usize 800#usize (by decide) (by change 800≤q.val.length;omega)
 simp only [NJS_Extract.verifier.candidate.canonical_scan_loop0_loop0.body,run,bind_tc_ok]
 change (do
   let bs←core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) q {start:=672#usize,«end»:=800#usize}
   let cf←core.result.Result.Insts.CoreOpsTry.branch (reply (ec bs))
   match cf with
   | .Continue _=>ok (done (none,1#u32))
   | .Break residual=>do
     let r←core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame NJS_Extract.verifier.Error) residual
     ok (done (some r,0#u32)))=_
 rw [sliced]
 change (do
   let cf←core.result.Result.Insts.CoreOpsTry.branch (reply (ec (trailing q)))
   match cf with
   | .Continue _=>ok (done (none,1#u32))
   | .Break residual=>do
     let r←core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame NJS_Extract.verifier.Error) residual
     ok (done (some r,0#u32)))=_
 cases h:ec (trailing q) <;> simp [reply,h,core.result.Result.Insts.CoreOpsTry.branch,
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

theorem entered (f : Array U8 4#usize→Option U32) (g : Slice U8→Option K)
 (ec : Slice U8→Bool) (q : Slice U8) (length : q.val.length=832)
 (iter : core.ops.range.Range Usize) (active : iter.start.val < iter.end.val)
 (bound : iter.start.val<4) :
 ∃ iter1,iter1.start.val=iter.start.val+1 ∧ iter1.end=iter.end ∧
 NJS_Extract.verifier.candidate.canonical_scan_loop0_loop0.body
   (fun b=>ok (f b)) (fun b=>ok (g b)) (fun b _=>ok (reply (ec b))) q iter none=
 ok (if slot f g q iter.start then cont (iter1,none) else done (some (.Err .Parse : ScanResult),0#u32)) := by
 obtain ⟨iter1,run,hs,he⟩:=NKB_CanonicalRange.next iter active
 have scalar:=NKB_CanonicalScalarLoop.source f g q iter.start length bound 26
   {start:=0#usize,«end»:=26#usize} rfl (by rfl)
 refine ⟨iter1,hs,he,?_⟩
 simp only [NJS_Extract.verifier.candidate.canonical_scan_loop0_loop0.body,run,bind_tc_ok]
 change (do
   let (p,i)←NJS_Extract.verifier.candidate.canonical_scan_loop0_loop0_loop0
     (fun b=>ok (f b)) (fun b=>ok (g b)) {start:=0#usize,«end»:=26#usize} q iter.start none
   match i with
   | 1#uscalar=>ok (cont (iter1,p))
   | _=>match p with | none=>ok (done (none,0#u32)) | some _=>ok (done (p,0#u32)))=_
 rw [scalar]
 change (do
   let (p,i)←ok (if slot f g q iter.start then (none,1#u32) else (some (.Err .Parse : ScanResult),0#u32))
   match i with
   | 1#uscalar=>ok (cont (iter1,p))
   | _=>match p with | none=>ok (done (none,0#u32)) | some _=>ok (done (p,0#u32)))=_
 cases h:slot f g q iter.start <;> simp [h] <;> rfl

#print axioms stop
#print axioms entered
end NKB_CanonicalOpening
