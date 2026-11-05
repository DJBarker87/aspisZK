import NHM_SharedPartials
import NHM_LoopDomain
set_option autoImplicit false
namespace NHM_SharedPartialsDomain
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues
open NHM_SharedPartials

def Inv (s : State) : Prop := s.1.end.val=4 ∧ s.1.start.val≤4 ∧ ∀ x∈s.2.val,canonE x

theorem preserves (f : Slice U8) (common : Array NQ 16#usize) (s t : State) (h : Inv s)
 (run : body f common s=ok (.cont t)) : Inv t := by
 obtain ⟨last,bound,canon⟩:=h
 obtain ⟨he,hi,active⟩:=progress f common s t run
 have hev:=congrArg (fun x : Usize=>x.val) he
 unfold body at run
 obtain ⟨⟨o,next⟩,hn,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 cases o with
 | none=>cases run
 | some side=>
  obtain ⟨reply,hr,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  cases reply with
  | Err e=>cases run
  | Ok value=>
   simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
   obtain ⟨after,ha,run⟩:=Port3_PushFrame.bind_success _ _ _ run
   have cv:=NHM_DotResult.partial_result f common side value (by rwa [NHM_PartialDot.cohort])
   have ca:=NHM_ArrayPreserve.canonical canonE s.2 after side value canon cv ha
   have same:=ControlFlow.cont.inj (Result.ok.inj run)
   refine ⟨by omega,by omega,?_⟩
   rw [←same]
   exact ca

theorem side_domain (s : State) (h : Inv s) (side : Usize) (next : NHI_RangeProgress.Range)
 (run : core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1=ok (some side,next)) : side.val<4 := by
 obtain ⟨same,last,inc,active⟩:=NHI_RangeProgress.some_next s.1 next side run
 have bound:=h.1
 subst side
 omega

theorem all_calls (f : Slice U8) (common : Array NQ 16#usize) :
 NHM_LoopDomain.all (body f common) Inv 5
  ({start:=0#usize,«end»:=4#usize},Array.repeat 4#usize NHI_Scalar.zero) := by
 apply NHM_LoopDomain.invariant _ _ (preserves f common)
 refine ⟨rfl,by change (0:Nat)≤4;omega,?_⟩
 intro x hx
 simp only [Array.repeat,List.mem_replicate] at hx
 rw [hx.2]
 exact NHI_Scalar.zero_canonical

#print axioms preserves
#print axioms side_domain
#print axioms all_calls
end NHM_SharedPartialsDomain
