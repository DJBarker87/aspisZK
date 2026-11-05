import NHX_FinalDomain
import NHI_ForwardRange
set_option autoImplicit false
namespace NHX_FinalTotal
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues
open NHX_FinalLoop

def Inv (s:State):Prop:=s.1.end.val=7 ∧ s.1.start.val≤7 ∧ canonE s.2

theorem active (parts powers:Cells) (hp:∀ x∈parts.val,canonE x) (hk:∀ x∈powers.val,canonE x)
 (s:State) (hs:Inv s) (bound:s.1.start.val<7) :
 ∃ t,body parts powers s=ok (.cont t) ∧ Inv t ∧ t.1.start.val=s.1.start.val+1 := by
 unfold Inv at hs
 obtain ⟨next,hn,hi,he⟩:=NHI_ForwardRange.active s.1 (by omega)
 have bi:s.1.start.val<(7#usize).val:=by exact bound
 let part:=NHI_ScalarDomain.pick parts s.1.start.val bi
 let power:=NHI_ScalarDomain.pick powers s.1.start.val bi
 have cp:=hp part (by exact List.getElem_mem _)
 have ck:=hk power (by exact List.getElem_mem _)
 obtain ⟨sum,hm,cm⟩:=NHX_FinalFold.cell_total s.2 power part hs.2.2 ck cp
 refine ⟨(next,sum),?_,⟨?_,?_,cm⟩,hi⟩
 · simp only [body,hn,bind_tc_ok]
   change (Array.index_usize parts s.1.start >>= fun a=>
    Array.index_usize powers s.1.start >>= fun b=>
    NHX_FinalFold.cell s.2 b a >>= fun c=>ok (.cont (next,c)))=ok (.cont (next,sum))
   simp only [NHI_ScalarDomain.index parts s.1.start bi,
    NHI_ScalarDomain.index powers s.1.start bi,bind_tc_ok,hm]
 · rw [he];exact hs.1
 · change next.start.val≤7
   omega

theorem unroll (parts powers:Cells) (hp:∀ x∈parts.val,canonE x) (hk:∀ x∈powers.val,canonE x)
 (fuel:Nat) (s:State) (hs:Inv s) (enough:7-s.1.start.val<fuel) :
 ∃ out,NHI_CountedLoop.unroll (body parts powers) fuel s=ok out ∧ canonE out := by
 induction fuel generalizing s with
 | zero=>omega
 | succ fuel ih=>
  by_cases active:s.1.start.val<7
  · obtain ⟨t,step,ht,inc⟩:=NHX_FinalTotal.active parts powers hp hk s hs active
    obtain ⟨out,run,co⟩:=ih t ht (by omega)
    exact ⟨out,by simp only [NHI_CountedLoop.unroll,step,bind_tc_ok,run],co⟩
  · have end7:=hs.1
    have stop:=NHI_ForwardRange.done s.1 (by omega)
    refine ⟨s.2,?_,hs.2.2⟩
    simp only [NHI_CountedLoop.unroll,body,stop,bind_tc_ok]
    rfl

theorem source (parts powers:Cells) (hp:∀ x∈parts.val,canonE x) (hk:∀ x∈powers.val,canonE x) :
 ∃ out,FIo_Native.weights.Weights.pair_loop17 {start:=0#usize,«end»:=7#usize} parts powers NHI_Scalar.zero=ok out ∧ canonE out := by
 rw [NHX_FinalLoop.source]
 exact unroll parts powers hp hk 8 _ ⟨rfl,by change (0:Nat)≤7;omega,NHI_Scalar.zero_canonical⟩ (by change (7:Nat)-0<8;omega)

#print axioms active
#print axioms unroll
#print axioms source
end NHX_FinalTotal
