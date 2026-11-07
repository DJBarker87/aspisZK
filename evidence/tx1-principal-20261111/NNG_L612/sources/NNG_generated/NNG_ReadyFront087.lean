import NNG_ReadySemantic087
import NNG_Split087
import NNG_FilledReturned087
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ReadyFront087
open Aeneas Aeneas.Std Result NMP_prepare NMP_PrepareSteps
abbrev Args:=NNG_PrepareInput087.Args

theorem split (a : Args) (obs : RSL.Observer) (env : RSL.Env) (logical : alloc.vec.Vec U8)
 (domain : RSL.TX1_087.Domain LIB_Instances.VL a obs) (size : logical.val.length=14759)
 (out : r1_semantic.Verified Unit) (v : verifier.View)
 (native : NNG_FrontValue087.split (NNG_PrepareEmission087.calls env) (NNG_PrepareInput087.input a obs env)
   logical=.ok (.Ok (out,v))) : NNG_ReadyView087.Ready out v := by
 obtain ⟨left,right,back,split,leftVal,rightVal,update⟩:=
  NNG_Split087.split (alloc.vec.Vec.deref logical) 13831#usize (by change 13831≤logical.val.length;rw [size];decide)
 have leftSize : left.val.length=13831:=by
  rw [leftVal,List.length_take]
  change min 13831 logical.val.length=13831
  rw [size]
  rfl
 have rightSize : right.val.length=928:=by
  rw [rightVal,List.length_drop]
  change logical.val.length-13831=928
  rw [size]
 have reconstruct : ∀ (sem after : Slice U8),sem.val.length=13831 → after.val.length=928 →
   ((alloc.vec.Vec.deref_mut logical).2 (back (sem,after))).val=sem.val++after.val:=by
  intro sem after semSize afterSize
  exact update sem after (semSize.trans leftSize.symm) (afterSize.trans rightSize.symm)
 unfold NNG_FrontValue087.split at native
 simp only [alloc.vec.Vec.deref_mut] at native
 change (do
  let pair←core.slice.Slice.split_at_mut (alloc.vec.Vec.deref logical) 13831#usize
  NNG_FrontValue087.semantic (NNG_PrepareEmission087.calls env) (NNG_PrepareInput087.input a obs env)
   pair.1.1 pair.1.2 pair.2 (alloc.vec.Vec.deref_mut logical).2)=.ok (.Ok (out,v)) at native
 rw [split,bind_tc_ok] at native
 exact NNG_ReadySemantic087.returned a obs env left right back (alloc.vec.Vec.deref_mut logical).2
  domain leftSize rightSize reconstruct out v native
#print axioms split

theorem returned (a : Args) (obs : RSL.Observer) (env : RSL.Env)
 (domain : RSL.TX1_087.Domain LIB_Instances.VL a obs)
 (out : r1_semantic.Verified Unit) (v : verifier.View)
 (native : NNG_FrontValue087.tree (NNG_PrepareEmission087.calls env) (NNG_PrepareInput087.input a obs env)=
   .ok (.Ok (out,v))) : NNG_ReadyView087.Ready out v := by
 unfold NNG_FrontValue087.tree at native
 obtain ⟨reply,filled,tail⟩:=NNG_ModelSuccess136.bind_out _ _ _ native
 cases reply with
 | Err e=>cases tail
 | Ok logical=>
  exact split a obs env logical domain (NNG_FilledReturned087.length env 14759#usize logical filled) out v tail
#print axioms returned
end AspisR1.NNG_ReadyFront087
