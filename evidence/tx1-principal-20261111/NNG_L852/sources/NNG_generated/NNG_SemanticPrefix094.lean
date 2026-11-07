import NNG_ValuesPrefix094
import NNG_ExpandedPrefix094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SemanticPrefix094
open Aeneas Aeneas.Std Result NMP_prepare NMP_PrepareSteps
abbrev Args := NNG_PrepareInput087.Args

theorem returned (a : Args) (obs : RSL.Observer) (env : RSL.Env) (semantic y1 : Slice U8)
 (back : SplitBack) (vecBack : VecBack)
 (domain : RSL.TX1_087.Domain LIB_Instances.VL a obs)
 (semSize : semantic.val.length=13831) (y1Size : y1.val.length=928)
 (reassemble : ∀ sem after : Slice U8,sem.val.length=13831 → after.val.length=928 →
  (vecBack (back (sem,after))).val=sem.val++after.val)
 (out : r1_semantic.Verified Unit) (v : verifier.View)
 (native : NNG_FrontValue087.semantic (NNG_PrepareEmission087.calls env) (NNG_PrepareInput087.input a obs env)
  semantic y1 back vecBack=.ok (.Ok (out,v))) :
 v.semantic.val.take 32=((NNG_PrepareInput087.input a obs env).bytes.val.drop 16).take 32 ∧ v.variant=.S2 := by
 let s:=NNG_PrepareInput087.input a obs env
 let src:=MultiproofConeSlices.sub s.bytes 16#usize 7031#usize
 have proofSize:=NNG_Slices087.proof_length a obs env domain
 have srcSize : src.val.length=7015 := MultiproofConeSlices.sub_length s.bytes _ _ (by decide) (by rw [proofSize];decide)
 have range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  s.bytes {start:=16#usize,«end»:=7031#usize}=.ok src :=
  MultiproofConeSlices.range_total _ _ _ (by decide) (by rw [proofSize];decide)
 let after:=LIBC_ExpandSemanticModel.output src
 have afterSize : after.val.length=13831 := by
  change (List.ofFn _).length=13831
  exact List.length_ofFn ..
 unfold NNG_FrontValue087.semantic at native
 rw [range] at native
 simp only [NNG_PrepareEmission087.calls,NNG_ExpandSemantic087.call,bind_tc_ok] at native
 have view := NNG_ValuesPrefix094.returned a obs env after y1 back vecBack domain afterSize y1Size
  (reassemble after · afterSize) out v native
 refine ⟨?_,view.2⟩
 rw [view.1,NNG_ExpandedPrefix094.first32 src (by rw [srcSize];decide)]
 change (((s.bytes.val.drop 16).take (7031-16)).take 32)=(s.bytes.val.drop 16).take 32
 rw [List.take_take]
 rfl
#print axioms returned
end AspisR1.NNG_SemanticPrefix094
