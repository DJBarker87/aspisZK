import NNG_SourceValues087
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceSemantic087
open Aeneas Aeneas.Std Result NMP_prepare NMP_PrepareSteps NMT_CallTree NNG_Observed136
abbrev Args := NNG_PrepareInput087.Args

theorem source (a : Args) (obs : RSL.Observer) (env : RSL.Env) (semantic y1 : Slice U8)
 (back : SplitBack) (vecBack : VecBack)
 (domain : RSL.TX1_087.Domain LIB_Instances.VL a obs)
 (semSize : semantic.val.length=13831) (y1Size : y1.val.length=928)
 (reassemble : ∀ (sem after : Slice U8),sem.val.length=13831 → after.val.length=928 →
   (vecBack (back (sem,after))).val=sem.val++after.val) :
 NNG_Canonical087.semantic LIB_Instances.VL a (LIB_Carriers.bytes semantic) (LIB_Carriers.bytes y1) env
  (observation (NNG_FrontProjection087.port a env) (NNG_Events087.events env)
   (NNG_Front087.semantic (NNG_PrepareEmission087.calls env) (NNG_PrepareInput087.input a obs env) semantic y1 back vecBack)) := by
 let s := NNG_PrepareInput087.input a obs env
 let src := MultiproofConeSlices.sub s.bytes 16#usize 7031#usize
 have proofSize := NNG_Slices087.proof_length a obs env domain
 have srcSize : src.val.length=7015 := MultiproofConeSlices.sub_length s.bytes _ _ (by decide) (by rw [proofSize];decide)
 have range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
   s.bytes {start:=16#usize,«end»:=7031#usize}=.ok src :=
   MultiproofConeSlices.range_total _ _ _ (by decide) (by rw [proofSize];decide)
 let head := invoke "TX1:098/expand_semantic" (src,semantic) (NNG_ExpandSemantic087.call src semantic)
 let k : (core.result.Result Unit compact.CodecError × Slice U8) → Code (NNG_Front087.FrontOut Unit) := fun pair=>
   match pair.1 with
   | .Err _=>pure (.Err verifier.Error.Parse)
   | .Ok _=>NNG_Front087.values (NNG_PrepareEmission087.calls env) s pair.2 y1 back vecBack
 have bodyObs : observation (NNG_FrontProjection087.port a env) (NNG_Events087.events env)
   (NNG_Front087.semantic (NNG_PrepareEmission087.calls env) s semantic y1 back vecBack)=
   observation (NNG_FrontProjection087.port a env) (NNG_Events087.events env) (NMT_CallTree.bind head k) := by
   unfold NNG_Front087.semantic
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
 have argEq : (LIB_Carriers.bytes src,LIB_Carriers.bytes semantic)=
   (RSL.slice a.proof RSL.OFF_SEMANTIC RSL.OFF_Y1,LIB_Carriers.bytes semantic) :=
   congrArg (fun bytes=>(bytes,LIB_Carriers.bytes semantic)) (NNG_Slices087.semantic_bytes a obs env domain)
 have nativeLaw := NNG_Occurrences087.semantic env src semantic srcSize semSize
 have childLaw := Eq.mp (congrArg (fun args=>LIBC_ExpandSemantic.child.run args env
   (observation NNG_ExpandSemantic087.port (NNG_Events087.events env) head)) argEq) nativeLaw
 have headLaw := NNG_MapError087.law LIB_Instances.VL.codecToV NNG_ExpandSemantic087.port
   (NNG_Events087.events env) head env
   (LIBC_ExpandSemantic.child.run (RSL.slice a.proof RSL.OFF_SEMANTIC RSL.OFF_Y1,LIB_Carriers.bytes semantic)) childLaw
 unfold NNG_Canonical087.semantic
 refine NNG_ResultBind137.sound head k
   (fun r=>NNG_MapError087.mapError LIB_Instances.VL.codecToV (NNG_ExpandSemantic087.port r))
   (NNG_FrontProjection087.port a env) (NNG_Events087.events env) env _ _ headLaw ?_
 intro pair returned
 have native := NNG_DLawStep136.invoke_returned (NNG_Events087.events env) "TX1:098/expand_semantic" _ _ _ returned
 have same : pair=(.Ok (),LIBC_ExpandSemanticModel.output src) := (Result.ok.inj native).symm
 subst pair
 let after := LIBC_ExpandSemanticModel.output src
 have afterSize : after.val.length=13831 := by
   change (List.ofFn _).length=13831
   exact List.length_ofFn
 change NNG_Canonical087.values LIB_Instances.VL a (LIB_Carriers.bytes after) (LIB_Carriers.bytes y1) env
   (observation _ _ (k (.Ok (),after)))
 exact NNG_SourceValues087.source a obs env after y1 back vecBack domain afterSize y1Size (reassemble after · afterSize ·)
#print axioms source
end AspisR1.NNG_SourceSemantic087
