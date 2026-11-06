import NKB_CanonicalScalar
set_option autoImplicit false
namespace NKB_CanonicalTail
open Aeneas Aeneas.Std Result ControlFlow AspisR1 NKB_CanonicalRange

def start (s : Usize) := Usize.wrapping_add (Usize.wrapping_mul s 120#usize) 104#usize
def finish (s : Usize) := Usize.wrapping_add (Usize.wrapping_mul s 120#usize) 120#usize
def window (q : Slice U8) (s : Usize) := MultiproofConeSlices.sub q (start s) (finish s)

theorem address (s : Usize) (slot : s.val<4) :
 (start s).val=s.val*120+104 ∧ (finish s).val=s.val*120+120 := by
 have mul:=Port3_Wrapping.wrap_mul_value s 120#usize (by scalar_tac)
 have a:=Port3_Wrapping.wrap_add_value (Usize.wrapping_mul s 120#usize) 104#usize (by scalar_tac)
 have b:=Port3_Wrapping.wrap_add_value (Usize.wrapping_mul s 120#usize) 120#usize (by scalar_tac)
 simp only [start,finish]
 simp only [show (120#usize).val=120 from rfl,show (104#usize).val=104 from rfl] at *
 exact ⟨by omega,by omega⟩

def accepted (f : Slice U8→Option K) (q : Slice U8) (s : Usize) : Bool :=
 (f (window q s)).isSome &&
 (f (NKB_CanonicalRange.window q s 0#usize)).isSome &&
 (f (NKB_CanonicalRange.window q s 1#usize)).isSome

/-- Source scalar-loop exit: C1 K then both K2 reads. Arbitrary pending
return is retained on continuation; a missing decoder reply is exactly Parse.
Native mates K025/K026 and K027/K028; no whole-loop native unwind. -/
theorem source (f : Array U8 4#usize→Option U32) (g : Slice U8→Option K)
 (q : Slice U8) (s : Usize) (iter : core.ops.range.Range Usize)
 (length : q.val.length=832) (slot : s.val<4) (ended : iter.end.val ≤ iter.start.val) :
 NJS_Extract.verifier.candidate.canonical_scan_loop0_loop0_loop0.body
   (fun b=>ok (f b)) (fun b=>ok (g b)) q s none iter=
 ok (done (if accepted g q s then (none,1#u32) else (some (.Err .Parse),0#u32))) := by
 obtain ⟨iter1,run⟩:=NKB_CanonicalRange.stop iter ended
 have a:=address s slot
 have sliced:=MultiproofConeSlices.range_total q (start s) (finish s) (by omega) (by omega)
 have pair:=NKB_CanonicalPair.source g q s length slot none
 simp only [NJS_Extract.verifier.candidate.canonical_scan_loop0_loop0_loop0.body,run,bind_tc_ok,lift]
 change (do
   let bs←core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) q {start:=start s,«end»:=finish s}
   let r←NJS_Extract.core.option.Option.ok_or (g bs) NJS_Extract.verifier.Error.Parse
   let cf←core.result.Result.Insts.CoreOpsTry.branch r
   match cf with
   | .Continue _=>do
     let p←NJS_Extract.verifier.candidate.canonical_scan_loop0_loop0_loop0_loop0 (fun b=>ok (g b)) {start:=0#usize,«end»:=2#usize} q s none
     match p with
     | none=>ok (done (none,1#u32))
     | some _=>ok (done (p,0#u32))
   | .Break residual=>do
     let r←core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame NJS_Extract.verifier.Error) residual
     ok (done (some r,0#u32)))=_
 rw [sliced]
 change (do
   let r←NJS_Extract.core.option.Option.ok_or (g (window q s)) NJS_Extract.verifier.Error.Parse
   let cf←core.result.Result.Insts.CoreOpsTry.branch r
   match cf with
   | .Continue _=>do
     let p←NJS_Extract.verifier.candidate.canonical_scan_loop0_loop0_loop0_loop0 (fun b=>ok (g b)) {start:=0#usize,«end»:=2#usize} q s none
     match p with
     | none=>ok (done (none,1#u32))
     | some _=>ok (done (p,0#u32))
   | .Break residual=>do
     let r←core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame NJS_Extract.verifier.Error) residual
     ok (done (some r,0#u32)))=_
 cases h:g (window q s) <;>
   cases h0:g (NKB_CanonicalRange.window q s 0#usize) <;>
   cases h1:g (NKB_CanonicalRange.window q s 1#usize) <;>
   simp [h,NJS_Extract.core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
     core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,pair,accepted,h0,h1]

#print axioms address
#print axioms source
end NKB_CanonicalTail
