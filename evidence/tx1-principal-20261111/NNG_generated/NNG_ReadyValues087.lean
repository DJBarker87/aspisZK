import NNG_ReadyView087
import NNG_Reassemble087
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ReadyValues087
open Aeneas Aeneas.Std Result NMP_prepare NMP_PrepareSteps
abbrev Args:=NNG_PrepareInput087.Args

theorem returned (a : Args) (obs : RSL.Observer) (env : RSL.Env) (semantic y1 : Slice U8)
 (back : SplitBack) (vecBack : VecBack)
 (domain : RSL.TX1_087.Domain LIB_Instances.VL a obs)
 (semSize : semantic.val.length=13831) (y1Size : y1.val.length=928)
 (reassemble : ∀ after : Slice U8,after.val.length=928 →
   (vecBack (back (semantic,after))).val=semantic.val++after.val)
 (out : r1_semantic.Verified Unit) (v : verifier.View)
 (native : NNG_FrontValue087.values (NNG_PrepareEmission087.calls env) (NNG_PrepareInput087.input a obs env)
   semantic y1 back vecBack=.ok (.Ok (out,v))) : NNG_ReadyView087.Ready out v := by
 let s:=NNG_PrepareInput087.input a obs env
 let src:=MultiproofConeSlices.sub s.bytes 7031#usize 7495#usize
 have proofSize:=NNG_Slices087.proof_length a obs env domain
 have srcSize : src.val.length=464:=MultiproofConeSlices.sub_length s.bytes _ _ (by decide) (by rw [proofSize];decide)
 have range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
   s.bytes {start:=7031#usize,«end»:=7495#usize}=.ok src:=
   MultiproofConeSlices.range_total _ _ _ (by decide) (by rw [proofSize];decide)
 let after:=LIBC_ExpandValuesModel.output src y1
 have afterSize : after.val.length=928:=by
  change (List.ofFn _).length=928
  rw [List.length_ofFn]
  exact y1Size
 have same:=reassemble after afterSize
 have first:=NNG_Reassemble087.prefix_window (vecBack (back (semantic,after))) semantic after same semSize
 have second:=NNG_Reassemble087.suffix (vecBack (back (semantic,after))) semantic after same semSize
 unfold NNG_FrontValue087.values at native
 rw [range] at native
 simp only [NNG_PrepareEmission087.calls,NNG_ExpandValues087.call,bind_tc_ok] at native
 change (do
  let fullSemantic←alloc.vec.Vec.index (core.slice.index.SliceIndexRangeToUsizeSlice U8) (vecBack (back (semantic,after))) {«end»:=13831#usize}
  let fullY1←alloc.vec.Vec.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8) (vecBack (back (semantic,after))) {start:=13831#usize}
  NNG_FrontValue087.view (NNG_PrepareEmission087.calls env) s fullSemantic fullY1)=.ok (.Ok (out,v)) at native
 rw [first,bind_tc_ok,second,bind_tc_ok] at native
 exact NNG_ReadyView087.view a obs env semantic after src y1 domain semSize srcSize y1Size
  (NNG_Slices087.r4 a obs env domain) rfl out v native
#print axioms returned
end AspisR1.NNG_ReadyValues087
