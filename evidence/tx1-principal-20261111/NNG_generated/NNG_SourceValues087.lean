import NNG_SourceView087
import NNG_Slices087
import NNG_Reassemble087
import NNG_Head087
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceValues087
open Aeneas Aeneas.Std Result NMP_prepare NMP_PrepareSteps NMT_CallTree NNG_Observed136
abbrev Args := NNG_PrepareInput087.Args

theorem source (a : Args) (obs : RSL.Observer) (env : RSL.Env) (semantic y1 : Slice U8)
 (back : SplitBack) (vecBack : VecBack)
 (domain : RSL.TX1_087.Domain LIB_Instances.VL a obs)
 (semSize : semantic.val.length=13831) (y1Size : y1.val.length=928)
 (reassemble : ∀ after : Slice U8,after.val.length=928 →
   (vecBack (back (semantic,after))).val=semantic.val++after.val) :
 NNG_Canonical087.values LIB_Instances.VL a (LIB_Carriers.bytes semantic) (LIB_Carriers.bytes y1) env
  (observation (NNG_FrontProjection087.port a env) (NNG_Events087.events env)
   (NNG_Front087.values (NNG_PrepareEmission087.calls env) (NNG_PrepareInput087.input a obs env) semantic y1 back vecBack)) := by
 let s := NNG_PrepareInput087.input a obs env
 let src := MultiproofConeSlices.sub s.bytes 7031#usize 7495#usize
 have proofSize := NNG_Slices087.proof_length a obs env domain
 have srcSize : src.val.length=464 := MultiproofConeSlices.sub_length s.bytes _ _ (by decide) (by rw [proofSize];decide)
 have range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
   s.bytes {start:=7031#usize,«end»:=7495#usize}=.ok src :=
   MultiproofConeSlices.range_total _ _ _ (by decide) (by rw [proofSize];decide)
 let head := invoke "TX1:099/expand_values" (src,y1) (NNG_ExpandValues087.call src y1)
 let k : (core.result.Result Unit compact.CodecError × Slice U8) → Code (NNG_Front087.FrontOut Unit) := fun pair=>
   match pair.1 with
   | .Err _=>pure (.Err verifier.Error.Parse)
   | .Ok _=> do
     let logical := vecBack (back (semantic,pair.2))
     let fullSemantic ← (alloc.vec.Vec.index (core.slice.index.SliceIndexRangeToUsizeSlice U8) logical {«end»:=13831#usize})
     let fullY1 ← (alloc.vec.Vec.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8) logical {start:=13831#usize})
     NNG_Front087.view (NNG_PrepareEmission087.calls env) s fullSemantic fullY1
 have bodyObs : observation (NNG_FrontProjection087.port a env) (NNG_Events087.events env)
   (NNG_Front087.values (NNG_PrepareEmission087.calls env) s semantic y1 back vecBack)=
   observation (NNG_FrontProjection087.port a env) (NNG_Events087.events env) (NMT_CallTree.bind head k) := by
   unfold NNG_Front087.values
   rw [range]
   change observation _ _ (NMT_CallTree.bind (Code.plain (.ok src) .done) _)=_
   rw [NNG_Head087.plain_ok]
   apply congrArg (observation (NNG_FrontProjection087.port a env) (NNG_Events087.events env))
   dsimp only [head]
   apply congrArg (NMT_CallTree.bind _)
   funext pair
   rcases pair with ⟨r,after⟩
   cases r <;> rfl
 rw [bodyObs]
 have argEq : (LIB_Carriers.bytes src,LIB_Carriers.bytes y1)=
   (RSL.slice a.proof RSL.OFF_Y1 RSL.OFF_INACTIVE,LIB_Carriers.bytes y1) :=
   congrArg (fun bytes=>(bytes,LIB_Carriers.bytes y1)) (NNG_Slices087.values_bytes a obs env domain)
 have nativeLaw := NNG_Occurrences087.values env src y1 srcSize y1Size
 have childLaw := Eq.mp (congrArg (fun args=>LIBC_ExpandValues.child.run args env
   (observation NNG_ExpandValues087.port (NNG_Events087.events env) head)) argEq) nativeLaw
 have headLaw := NNG_MapError087.law LIB_Instances.VL.codecToV NNG_ExpandValues087.port
   (NNG_Events087.events env) head env
   (LIBC_ExpandValues.child.run (RSL.slice a.proof RSL.OFF_Y1 RSL.OFF_INACTIVE,LIB_Carriers.bytes y1)) childLaw
 unfold NNG_Canonical087.values
 refine NNG_ResultBind137.sound head k
   (fun r=>NNG_MapError087.mapError LIB_Instances.VL.codecToV (NNG_ExpandValues087.port r))
   (NNG_FrontProjection087.port a env) (NNG_Events087.events env) env _ _ headLaw ?_
 intro pair returned
 have native := NNG_DLawStep136.invoke_returned (NNG_Events087.events env) "TX1:099/expand_values" _ _ _ returned
 have same : pair=(.Ok (),LIBC_ExpandValuesModel.output src y1) := (Result.ok.inj native).symm
 subst pair
 let after := LIBC_ExpandValuesModel.output src y1
 have afterSize : after.val.length=928 := by
   change (List.ofFn _).length=928
   rw [List.length_ofFn]
   exact y1Size
 have sameLogical := reassemble after afterSize
 have first := NNG_Reassemble087.prefix_window (vecBack (back (semantic,after))) semantic after sameLogical semSize
 have second := NNG_Reassemble087.suffix (vecBack (back (semantic,after))) semantic after sameLogical semSize
 change NNG_Canonical087.view LIB_Instances.VL a (LIB_Carriers.bytes semantic) (LIB_Carriers.bytes after) env
   (observation _ _ (k (.Ok (),after)))
 have tailObs : observation (NNG_FrontProjection087.port a env) (NNG_Events087.events env) (k (.Ok (),after))=
   observation (NNG_FrontProjection087.port a env) (NNG_Events087.events env)
     (NNG_Front087.view (NNG_PrepareEmission087.calls env) s semantic after) := by
   dsimp only [k]
   rw [first]
   change observation _ _ (NMT_CallTree.bind (Code.plain (.ok semantic) .done) _)=_
   rw [NNG_Head087.plain_ok,second]
   rfl
 rw [tailObs]
 exact NNG_SourceView087.source a obs env semantic after domain proofSize semSize afterSize
#print axioms source
end AspisR1.NNG_SourceValues087
