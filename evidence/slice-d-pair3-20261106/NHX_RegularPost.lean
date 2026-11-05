import NHX_ProcessPost
import NHM_RegularKinds
import NHM_RegularDomain
set_option autoImplicit false
noncomputable section
namespace NHX_RegularPost
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
abbrev Vec:=NHX_ProcessReference.Vec
abbrev Parts:=NHX_ProcessReference.Parts
abbrev Reply:=NHX_ProcessReference.Reply
abbrev Powers:=NHX_ProcessReference.Powers
variable [FIo_Native.Allocation]

def Inv (v : Vec) (p : Parts) : Prop:=
 NHI_CellCanon.slice (alloc.vec.Vec.deref v) ∧ (alloc.vec.Vec.deref v).val.length=64 ∧ NHX_ProcessPost.PartsCanon p

def Valid (kind : Usize) : Prop:=kind.val=1∨kind.val=2∨kind.val=3∨kind.val=5∨kind.val=6

theorem go (w:FIo_Native.weights.Weights) (alpha:Slice NE) (f:Slice U8) (ap0 ap1:Powers)
 (s2:w.variant=FIo_Native.transport.Variant.S2) (hf:NHI_TensorOuterStep.Factors w)
 (ha:∀ x∈ap0.val,canonE x) (hb:∀ x∈ap1.val,canonE x)
 (ks:List Usize) (valid:∀ k∈ks,Valid k) (before after:Vec) (parts out:Parts) (reply:Reply)
 (initial:Inv before parts)
 (run:NHM_RegularKinds.go
  (fun k s p=>FIo_Native.weights.process_kind w k alpha f 2#usize 64#usize ap0 ap1 s p)
  ks before parts=ok (reply,after,out)) : Inv after out := by
 induction ks generalizing before parts with
 | nil=>
  simp only [NHM_RegularKinds.go] at run
  obtain ⟨_,rest⟩:=Prod.mk.inj (Result.ok.inj run)
  obtain ⟨hv,hp⟩:=Prod.mk.inj rest
  subst after;subst out
  exact initial
 | cons k rest ih=>
  have vk:=valid k (by simp)
  simp only [NHM_RegularKinds.go] at run
  obtain ⟨⟨r,v1,p1⟩,hr,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  have hr1:NHX_ProcessReference.reference w k f ap0 ap1 before parts=ok (r,v1,p1):=by
   rwa [←NHX_ProcessReference.source w k alpha f ap0 ap1 before parts s2]
  have post:=NHX_ProcessPost.post w k f ap0 ap1 before v1 parts p1 r vk hf ha hb initial.1 initial.2.1 initial.2.2 hr1
  have next:Inv v1 p1:=⟨post.1,post.2.1,post.2.2.1⟩
  change ((core.result.Result.Insts.CoreOpsTry.branch r) >>= fun cf=>
   match cf with
   | core.ops.control_flow.ControlFlow.Continue _=>(NHM_RegularKinds.go (fun k s p=>FIo_Native.weights.process_kind w k alpha f 2#usize 64#usize ap0 ap1 s p) rest v1 p1)
   | core.ops.control_flow.ControlFlow.Break residual=>
      (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit
       (core.convert.FromSame FIo_Native.verifier.Error) residual >>= fun rr=>ok (rr,v1,p1)))=ok (reply,after,out) at run
  cases r with
  | Err e=>
   simp only [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame,lift,bind_tc_ok] at run
   obtain ⟨_,rs⟩:=Prod.mk.inj (Result.ok.inj run)
   obtain ⟨hv,hp⟩:=Prod.mk.inj rs
   subst after;subst out
   exact next
  | Ok unit=>
   cases unit
   simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
   exact ih (fun k hk=>valid k (by simp [hk])) v1 p1 next run

theorem source (w:FIo_Native.weights.Weights) (shared:Bool) (alpha:Slice NE) (f:Slice U8) (ap0 ap1:Powers)
 (s2:w.variant=FIo_Native.transport.Variant.S2) (hf:NHI_TensorOuterStep.Factors w)
 (ha:∀ x∈ap0.val,canonE x) (hb:∀ x∈ap1.val,canonE x)
 (before after:Vec) (parts out:Parts) (reply:Reply) (initial:Inv before parts)
 (run:FIo_Native.weights.process_regular_kinds w shared alpha f 2#usize 64#usize ap0 ap1 before parts=ok (reply,after,out)) :
 Inv after out := by
 rw [NHM_RegularKinds.cohort] at run
 exact go w alpha f ap0 ap1 s2 hf ha hb (NHM_RegularKinds.kinds shared)
  (fun k hk=>NHM_RegularDomain.membership shared k hk) before after parts out reply initial run

#print axioms go
#print axioms source
end NHX_RegularPost
end
