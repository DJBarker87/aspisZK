import NKB_ScanWindows
import NJS_KeyStep
set_option autoImplicit false
namespace NKB_CanonicalRange
open Aeneas Aeneas.Std Result ControlFlow AspisR1

abbrev ScanResult := core.result.Result Unit NJS_Extract.verifier.Error
abbrev Pending := Option ScanResult
abbrev K := NJS_Extract.aspis_core.field.QM31

theorem next (iter : core.ops.range.Range Usize) (active : iter.start.val < iter.end.val) :
 ∃ iter1, core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=
   ok (some iter.start,iter1) ∧ iter1.start.val=iter.start.val+1 ∧ iter1.end=iter.end := by
 obtain ⟨⟨o,iter1⟩,run,ho,hs,he⟩ := WP.spec_imp_exists
   (core.iter.range.IteratorRange.next_UScalar_some_spec
     (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
     (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x;rfl) (by intro x y;rfl) iter active)
 subst o
 exact ⟨iter1,run,hs,he⟩

theorem stop (iter : core.ops.range.Range Usize) (ended : iter.end.val ≤ iter.start.val) :
 ∃ iter1, core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=ok (none,iter1) := by
 obtain ⟨⟨o,iter1⟩,run,ho,_⟩ := WP.spec_imp_exists
   (core.iter.range.IteratorRange.next_UScalar_none_spec
     (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
     (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x y;rfl) iter ended)
 subst o
 exact ⟨iter1,run⟩

def start (s l : Usize) := Usize.wrapping_add
 (Usize.wrapping_add 480#usize (Usize.wrapping_mul s 32#usize))
 (Usize.wrapping_mul l 16#usize)
def finish (s l : Usize) := Usize.wrapping_add (start s l) 16#usize
def window (q : Slice U8) (s l : Usize) := MultiproofConeSlices.sub q (start s l) (finish s l)

theorem address (s l : Usize) (slot : s.val<4) (lane : l.val<2) :
 (start s l).val=480+s.val*32+l.val*16 ∧
 (finish s l).val=480+s.val*32+l.val*16+16 := by
 have sm : (Usize.wrapping_mul s 32#usize).val=s.val*32 :=
   Port3_Wrapping.wrap_mul_value s 32#usize (by scalar_tac)
 have lm : (Usize.wrapping_mul l 16#usize).val=l.val*16 :=
   Port3_Wrapping.wrap_mul_value l 16#usize (by scalar_tac)
 have a := Port3_Wrapping.wrap_add_value 480#usize (Usize.wrapping_mul s 32#usize) (by scalar_tac)
 have b := Port3_Wrapping.wrap_add_value
   (Usize.wrapping_add 480#usize (Usize.wrapping_mul s 32#usize)) (Usize.wrapping_mul l 16#usize) (by scalar_tac)
 have c := Port3_Wrapping.wrap_add_value (start s l) 16#usize (by simp only [start] at *;scalar_tac)
 simp only [start,finish] at *
 simp only [show (480#usize).val=480 from rfl,show (16#usize).val=16 from rfl] at *
 exact ⟨by omega,by omega⟩

theorem entered (f : Slice U8→Option K) (q : Slice U8) (s : Usize) (p : Pending)
 (iter : core.ops.range.Range Usize) (size : q.val.length=832)
 (slot : s.val<4) (lane : iter.start.val<2) (active : iter.start.val < iter.end.val) :
 ∃ iter1,iter1.start.val=iter.start.val+1 ∧ iter1.end=iter.end ∧
 NJS_Extract.verifier.candidate.canonical_scan_loop0_loop0_loop0_loop0.body
   (fun bs=>ok (f bs)) q s p iter=
   ok (match f (window q s iter.start) with
     | none=>done (some (.Err .Parse)) | some _=>cont iter1) := by
 obtain ⟨iter1,run,hs,he⟩:=next iter active
 have a:=address s iter.start slot lane
 have slice:=MultiproofConeSlices.range_total q (start s iter.start) (finish s iter.start)
   (by omega) (by omega)
 refine ⟨iter1,hs,he,?_⟩
 simp only [NJS_Extract.verifier.candidate.canonical_scan_loop0_loop0_loop0_loop0.body,
   run,bind_tc_ok,lift]
 change (do
   let bs ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) q
     {start:=start s iter.start, «end»:=finish s iter.start}
   let r ← NJS_Extract.core.option.Option.ok_or (f bs) NJS_Extract.verifier.Error.Parse
   let cf ← core.result.Result.Insts.CoreOpsTry.branch r
   match cf with
   | .Continue _ => ok (cont iter1)
   | .Break residual => do
     let r1 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
       Unit (core.convert.FromSame NJS_Extract.verifier.Error) residual
     ok (done (some r1)))=_
 rw [slice]
 cases h:f (window q s iter.start) <;>
   simp only [window] at h <;>
   simp [h,NJS_Extract.core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
     core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
     core.convert.FromSame]

#print axioms next
#print axioms stop
#print axioms address
#print axioms entered
end NKB_CanonicalRange
