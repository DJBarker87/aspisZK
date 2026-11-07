import NNG_SourceSemantic087
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceSplit087
open Aeneas Aeneas.Std Result NMP_prepare NMP_PrepareSteps NMT_CallTree NNG_Observed136
abbrev Args := NNG_PrepareInput087.Args

theorem source (a : Args) (obs : RSL.Observer) (env : RSL.Env) (logical : alloc.vec.Vec U8)
 (domain : RSL.TX1_087.Domain LIB_Instances.VL a obs) (size : logical.val.length=14759) :
 NNG_Canonical087.semantic LIB_Instances.VL a
  ((LIB_Carriers.bytes (alloc.vec.Vec.deref logical)).take RSL.LOGICAL_SEMANTIC)
  ((LIB_Carriers.bytes (alloc.vec.Vec.deref logical)).drop RSL.LOGICAL_SEMANTIC) env
  (observation (NNG_FrontProjection087.port a env) (NNG_Events087.events env)
   (NNG_Front087.split (NNG_PrepareEmission087.calls env) (NNG_PrepareInput087.input a obs env) logical)) := by
 obtain ⟨left,right,back,split,leftVal,rightVal,update⟩ :=
   NNG_Split087.split (alloc.vec.Vec.deref logical) 13831#usize (by change 13831≤logical.val.length;rw [size];decide)
 have leftSize : left.val.length=13831 := by
   rw [leftVal,List.length_take]
   change min 13831 logical.val.length=13831
   rw [size]
   rfl
 have rightSize : right.val.length=928 := by
   rw [rightVal,List.length_drop]
   change logical.val.length-13831=928
   rw [size]
 have leftBytes : LIB_Carriers.bytes left=(LIB_Carriers.bytes (alloc.vec.Vec.deref logical)).take RSL.LOGICAL_SEMANTIC := by
   change left.val.map _=(logical.val.map _).take 13831
   rw [leftVal,List.map_take]
   rfl
 have rightBytes : LIB_Carriers.bytes right=(LIB_Carriers.bytes (alloc.vec.Vec.deref logical)).drop RSL.LOGICAL_SEMANTIC := by
   change right.val.map _=(logical.val.map _).drop 13831
   rw [rightVal,List.map_drop]
   rfl
 have reconstruct : ∀ (sem after : Slice U8),sem.val.length=13831 → after.val.length=928 →
   ((alloc.vec.Vec.deref_mut logical).2 (back (sem,after))).val=sem.val++after.val := by
   intro sem after semSize afterSize
   exact update sem after (semSize.trans leftSize.symm) (afterSize.trans rightSize.symm)
 have bodyObs : observation (NNG_FrontProjection087.port a env) (NNG_Events087.events env)
   (NNG_Front087.split (NNG_PrepareEmission087.calls env) (NNG_PrepareInput087.input a obs env) logical)=
   observation (NNG_FrontProjection087.port a env) (NNG_Events087.events env)
   (NNG_Front087.semantic (NNG_PrepareEmission087.calls env) (NNG_PrepareInput087.input a obs env) left right back (alloc.vec.Vec.deref_mut logical).2) := by
   unfold NNG_Front087.split
   simp only [alloc.vec.Vec.deref_mut]
   change observation _ _ (NMT_CallTree.bind (invoke "std/split_at_mut" (alloc.vec.Vec.deref logical,13831#usize)
     (core.slice.Slice.split_at_mut (alloc.vec.Vec.deref logical) 13831#usize)) _)=_
   rw [split]
   rw [NNG_Head087.invoke_ok _ env _ _ _ _ (NNG_Events087.silent env _ _ _ (by decide) (by decide))]
 have source := NNG_SourceSemantic087.source a obs env left right back (alloc.vec.Vec.deref_mut logical).2 domain leftSize rightSize reconstruct
 have source' := Eq.mp (congrArg (fun o=>NNG_Canonical087.semantic LIB_Instances.VL a (LIB_Carriers.bytes left) (LIB_Carriers.bytes right) env o) bodyObs.symm) source
 exact Eq.mp (congrArg (fun args=>NNG_Canonical087.semantic LIB_Instances.VL a args.1 args.2 env
   (observation (NNG_FrontProjection087.port a env) (NNG_Events087.events env)
     (NNG_Front087.split (NNG_PrepareEmission087.calls env) (NNG_PrepareInput087.input a obs env) logical)))
   (congrArg₂ Prod.mk leftBytes rightBytes)) source'
#print axioms source
end AspisR1.NNG_SourceSplit087
