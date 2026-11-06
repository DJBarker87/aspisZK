import NKB_CanonicalPair
set_option autoImplicit false
namespace NKB_CanonicalScalar
open Aeneas Aeneas.Std Result ControlFlow AspisR1 NKB_CanonicalRange

def start (s l : Usize) := Usize.wrapping_add (Usize.wrapping_mul s 120#usize) (Usize.wrapping_mul l 4#usize)
def finish (s l : Usize) := Usize.wrapping_add (start s l) 4#usize

theorem address (s l : Usize) (slot : s.val<4) (lane : l.val<26) :
 (start s l).val=s.val*120+l.val*4 ∧ (finish s l).val=s.val*120+l.val*4+4 := by
 have sm:=Port3_Wrapping.wrap_mul_value s 120#usize (by scalar_tac)
 have lm:=Port3_Wrapping.wrap_mul_value l 4#usize (by scalar_tac)
 have a:=Port3_Wrapping.wrap_add_value (Usize.wrapping_mul s 120#usize) (Usize.wrapping_mul l 4#usize) (by scalar_tac)
 have b:=Port3_Wrapping.wrap_add_value (start s l) 4#usize (by simp only [start] at *;scalar_tac)
 simp only [start,finish] at *
 simp only [show (120#usize).val=120 from rfl,show (4#usize).val=4 from rfl] at *
 exact ⟨by omega,by omega⟩

def window (q : Slice U8) (s l : Usize) := MultiproofConeSlices.sub q (start s l) (finish s l)

theorem size (q : Slice U8) (s l : Usize) (length : q.val.length=832)
 (slot : s.val<4) (lane : l.val<26) : (window q s l).val.length=4 := by
 have a:=address s l slot lane
 rw [window,MultiproofConeSlices.sub_length q (start s l) (finish s l) (by omega) (by omega)]
 omega

/-- One reached scalar read, full Err(Parse) or continuation, with the exact
four copied bytes. Payloads are unused by the native caller. K029/K030. -/
theorem entered (f : Array U8 4#usize→Option U32) (g : Slice U8→Option K)
 (q : Slice U8) (s : Usize) (p : Pending) (iter : core.ops.range.Range Usize)
 (length : q.val.length=832) (slot : s.val<4) (lane : iter.start.val<26)
 (active : iter.start.val < iter.end.val) :
 ∃ iter1,iter1.start.val=iter.start.val+1 ∧ iter1.end=iter.end ∧
 NJS_Extract.verifier.candidate.canonical_scan_loop0_loop0_loop0.body
   (fun b=>ok (f b)) (fun b=>ok (g b)) q s p iter=
 ok (match f (⟨(window q s iter.start).val,size q s iter.start length slot lane⟩ : Array U8 4#usize) with
 | none=>done (some (.Err .Parse),0#u32) | some _=>cont iter1) := by
 obtain ⟨iter1,run,hs,he⟩:=NKB_CanonicalRange.next iter active
 have a:=address s iter.start slot lane
 have sliced:=MultiproofConeSlices.range_total q (start s iter.start) (finish s iter.start) (by omega) (by omega)
 have len:=size q s iter.start length slot lane
 let b : Array U8 4#usize:=⟨(window q s iter.start).val,len⟩
 have copied : core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 (window q s iter.start)=ok (.Ok b) := by
   simp [core.array.TryFromArrayCopySlice.try_from,len,b]
 refine ⟨iter1,hs,he,?_⟩
 simp only [NJS_Extract.verifier.candidate.canonical_scan_loop0_loop0_loop0.body,run,bind_tc_ok,lift]
 change (do
   let bs←core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) q {start:=start s iter.start,«end»:=finish s iter.start}
   let r←core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 bs
   let a←core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
   let r←NJS_Extract.core.option.Option.ok_or (f a) NJS_Extract.verifier.Error.Parse
   let cf←core.result.Result.Insts.CoreOpsTry.branch r
   match cf with
   | .Continue _=>ok (cont iter1)
   | .Break residual=>do
     let r←core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame NJS_Extract.verifier.Error) residual
     ok (done (some r,0#u32)))=_
 rw [sliced]
 change (do
   let r←core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 (window q s iter.start)
   let a←core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
   let r←NJS_Extract.core.option.Option.ok_or (f a) NJS_Extract.verifier.Error.Parse
   let cf←core.result.Result.Insts.CoreOpsTry.branch r
   match cf with
   | .Continue _=>ok (cont iter1)
   | .Break residual=>do
     let r←core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame NJS_Extract.verifier.Error) residual
     ok (done (some r,0#u32)))=_
 rw [copied]
 cases h:f b <;> simp [core.result.Result.unwrap,b,h,NJS_Extract.core.option.Option.ok_or,
   core.result.Result.Insts.CoreOpsTry.branch,
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

#print axioms address
#print axioms size
#print axioms entered
end NKB_CanonicalScalar
