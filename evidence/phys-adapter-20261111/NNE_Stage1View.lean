import NNE_Observed
import NNE_RslError
import NNE_AbortRollback
set_option autoImplicit false
noncomputable section
namespace NNE_Stage1View
open Aeneas Aeneas.Std Result AspisR1 S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_ReturnedCheckpoint Hist_Store Hist_RuntimeEntry CPP_BankState
open RSL RSL.TAS NNE_Observed
variable (S : Sig) (d : NNE_AcceptanceSig.Data S) (V : VLib)
 (P : PreparedNew V) (C : TX1_345.S1Lib V) (c : S.Ctx)
 (a1 : NND_A1 (NNE_AcceptanceSig.physical S d) V P C)
 (hx : S.Exhibited c)
 (before after : Bank) (input : CPP_Invocation.Invocation Bool) (env : Env)
 (envrep : S.EnvRep c env) (post : SdkState) (es : List Event) (event : S2X.AccountEvent)

include a1 hx envrep

/-- Complete store/event result for an actual successful stage1 occurrence. -/
theorem success
 (route : Hiq_ReleaseRoute.stage1 input.call.data)
 (href : TX1_344.Ref V P C (args before input (d.program c)) (state before input) env
   ⟨.ret (.ok (),post),es⟩)
 (rep : Assoc before after input ⟨.ret (.ok (),post),es⟩ event) :
 CPP_BankState.apply (d.native1 (S.model1 c)) (d.native2 (S.model2 c)) d.copy
   NNE_AbortIndicator.allocator (d.program c) before (.invoke input) = (after,event) := by
 obtain ⟨xs,mid,ck,acc2,es1,es2,es3,hgood,hs,hc,ha,hw,he⟩ :=
  NNE_RslOk.first_ok V P C _ _ _ _ _ href
 have count : input.count = 3 := by
  have hg := (NNE_Route.first_guard _ _ input.call.data).mp hgood
  simpa [args,NNE_EntryArgs.args] using hg.2
 have hstate : input.call.state = true := rep.1
 obtain ⟨saved,hout⟩ := rep.2.2.2.2 route count
 have href' : TX1_344.Ref V P C
   (NNE_EntryArgs.args (entry before input) 3 (d.program c) input.call.data)
   (NNE_Entry.state (entry before input) 0) env ⟨.ret (.ok (),post),es⟩ := by
  simpa only [args,state,count] using href
 have accepted := NNE_PhysicalAccepted.first V P C d.err d.invalid
   (d.native1 (S.model1 c)) d.copy d.std (entry before input) (d.program c)
   input.call.data env saved post es href' hout (by
    intro es' hchild
    exact (a1.stage1 c _ env _ _ hx envrep hchild rfl
      (entry before input) (d.program c) input.call.data rfl).1 saved rfl)
 have hs' : TX2_240.snapAll
   ((List.range 3).map (NNE_Entry.account (entry before input))) TX1_344.snapLens
   (NNE_Entry.state (entry before input) 0) env ⟨.ret (xs,mid),es1⟩ := by
  simpa only [args,state,NNE_EntryArgs.args,count] using hs
 obtain ⟨_,hmid⟩ := NNE_SnapshotSequence.first d.err d.invalid (entry before input) 0 env xs mid es1 hs'
 subst mid
 have ha' : acc2 = NNE_Entry.account (entry before input) 2 := by
  simpa [args,NNE_EntryArgs.args,count] using ha.symm
 subst acc2
 obtain ⟨write,_,token,pre,tail,hev,_,_⟩ := NNE_CopyFrame.copy_ok _ _ _ _ _ _ hw
 have mem : Event.write (NNE_Entry.account (entry before input) 2).cell ck ∈ es := by
  rw [he,hev]; simp
 have hck := hout _ _ mem
 rw [hck] at write mem
 have afterEq := NNE_BankImage.copy before after (entry before input) 3 post saved
   (NNE_BankImage.loaded before _ 3) rep.2.1 rep.2.2.1 write
 have eventEq := NNE_BankImage.write es event rep.2.2.2.1 _ saved mem
 have rout : Hiq_ReleaseRoute.route (CPP_BankState.invocation before input).call.data = .first :=
  (Hiq_ReleaseRoute.first_iff _).mpr route
 have hcall : CPP_Invocation.first (d.native1 (S.model1 c)) d.copy
   NNE_AbortIndicator.allocator (d.program c) before.cells (CPP_BankState.invocation before input) =
   ok (.Ok (saved,S2W_WrapperLaws.writeBracket (entry before input).heap 2 0 0
    (S2W_CommittedCheckpoint.source (nativeBytes saved)),true)) := by
  simpa only [CPP_Invocation.first,CPP_BankState.invocation,route,count,and_self,ite_true,hstate,entry]
   using accepted
 simp only [CPP_BankState.apply,CPP_Invocation.native,rout,hcall,Hir_Call.firstEffect]
 rw [afterEq,eventEq]
 rfl
#print axioms success
end NNE_Stage1View
end
