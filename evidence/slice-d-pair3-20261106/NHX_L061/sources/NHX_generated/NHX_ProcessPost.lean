import NHX_ProcessReference
import NHM_DotFinishCanonical
import NHM_ArrayPreserve
set_option autoImplicit false
noncomputable section
namespace NHX_ProcessPost
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
open NHX_ProcessReference
variable [FIo_Native.Allocation]

def PartsCanon (parts : Parts) : Prop:=∀ x∈parts.val,canonE x

theorem post (w : FIo_Native.weights.Weights) (kind : Usize) (f : Slice U8)
 (ap0 ap1 : Powers) (scratch after : Vec) (parts out : Parts) (reply : Reply)
 (member:kind.val=1∨kind.val=2∨kind.val=3∨kind.val=5∨kind.val=6)
 (hf:NHI_TensorOuterStep.Factors w) (ha:∀ x∈ap0.val,canonE x) (hb:∀ x∈ap1.val,canonE x)
 (hs:NHI_CellCanon.slice (alloc.vec.Vec.deref scratch)) (len:(alloc.vec.Vec.deref scratch).val.length=64)
 (hp:PartsCanon parts) (run:reference w kind f ap0 ap1 scratch parts=ok (reply,after,out)) :
 NHI_CellCanon.slice (alloc.vec.Vec.deref after) ∧ (alloc.vec.Vec.deref after).val.length=64 ∧
 PartsCanon out ∧ (∀ j:Nat,j≠kind.val→ out.val[j]?=parts.val[j]?) := by
 obtain ⟨hk,hkind⟩:=NHX_KindIndex.selected kind member
 let k:=NHX_KindIndex.native kind
 obtain ⟨s,ht,cs,ls⟩:=NHX_ProcessPorts.tensor w k hk hf scratch len hs
 let row:=NHI_ScalarDomain.pick w.factors k.val hk
 have ir:=NHI_ScalarDomain.index w.factors k hk
 have cr:∀ d (hd:d<5),NHI_CellCanon.array (NHI_ScalarDomain.pick row d hd):=hf k.val hk
 obtain ⟨scale,hscale,cscale⟩:=NHX_HighReference.scale_total row ap0 ap1 cr ha hb
 dsimp only [k,row] at ht ir hscale
 unfold reference at run
 simp only [ht,ir,hscale,NHM_DotInitial.source,bind_tc_ok] at run
 obtain ⟨⟨r,dot⟩,hdot,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 change NHX_ProcessReference.afterBytes kind scale ((alloc.vec.Vec.deref_mut scratch).2 s) parts r dot=ok (reply,after,out) at run
 unfold NHX_ProcessReference.afterBytes at run
 cases r with
 | Err e=>
  simp only [core.result.Result.Insts.CoreOpsTry.branch,
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
   core.convert.FromSame,lift,bind_tc_ok] at run
  obtain ⟨_,rest⟩:=Prod.mk.inj (Result.ok.inj run)
  obtain ⟨sameA,sameP⟩:=Prod.mk.inj rest
  subst after;subst out
  exact ⟨cs,ls,hp,fun _ _=>rfl⟩
 | Ok unit=>
  cases unit
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
  obtain ⟨value,hvalue,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  have cv:=NHM_DotFinishCanonical.source dot value hvalue
  obtain ⟨product,hproduct,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  have cp:=NHX_FieldResults.wide_mul scale value product cscale cv hproduct
  obtain ⟨parts1,hparts,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  have cparts:=NHM_ArrayPreserve.canonical canonE parts parts1 kind product hp cp hparts
  obtain ⟨_,rest⟩:=Prod.mk.inj (Result.ok.inj run)
  obtain ⟨sameA,sameP⟩:=Prod.mk.inj rest
  subst after;subst out
  exact ⟨cs,ls,cparts,fun j hj=>NHM_ArrayPreserve.frame parts parts1 kind product hparts j hj⟩

#print axioms post
end NHX_ProcessPost
end
