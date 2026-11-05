import NHX_LowScale
import NHX_FieldResults
import NHM_LoopDomain
import NHM_ArrayPreserve
set_option autoImplicit false
namespace NHX_LowDomain
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues
abbrev Powers:=Array NE 4#usize
abbrev Cells:=Array NE 16#usize
abbrev State:=NHI_RangeProgress.Range×Cells

def body (ap0 ap1:Powers) (s:State):=FIo_Native.weights.Weights.pair_loop15.body ap0 ap1 s.1 s.2

theorem preserves (ap0 ap1:Powers) (ha:∀ x∈ap0.val,canonE x) (hb:∀ x∈ap1.val,canonE x)
 (s t:State) (hs:∀ x∈s.2.val,canonE x) (run:body ap0 ap1 s=ok (.cont t)) :
 ∀ x∈t.2.val,canonE x := by
 unfold body FIo_Native.weights.Weights.pair_loop15.body at run
 obtain ⟨⟨o,next⟩,hn,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 cases o with
 | none=>cases run
 | some j=>
  obtain ⟨i,hi,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i1,hi1,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨x,hx,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i2,hi2,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i3,hi3,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨y,hy,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨product,hm,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  simp only [NHX_LowScale.square,bind_tc_ok] at run
  obtain ⟨scaled,hscaled,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨out,hout,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  have cx:=NHM_ArrayCanon.read canonE ap0 i1 x ha hx
  have cy:=NHM_ArrayCanon.read canonE ap1 i3 y hb hy
  have cp:=NHX_FieldResults.wide_mul x y product cx cy hm
  obtain ⟨result,hr,cr,values⟩:=NHX_LowScale.total product
  rw [hscaled] at hr
  cases Result.ok.inj hr
  have co:=NHM_ArrayPreserve.canonical canonE s.2 out j scaled hs cr hout
  have same:=ControlFlow.cont.inj (Result.ok.inj run)
  rw [←same]
  exact co

theorem all_calls (ap0 ap1:Powers) (ha:∀ x∈ap0.val,canonE x) (hb:∀ x∈ap1.val,canonE x)
 (s:State) (hs:∀ x∈s.2.val,canonE x) : NHM_LoopDomain.all (body ap0 ap1)
 (fun s=>∀ x∈s.2.val,canonE x) 17 s :=
 NHM_LoopDomain.invariant (body ap0 ap1) (fun s=>∀ x∈s.2.val,canonE x)
 (fun s t hs run=>preserves ap0 ap1 ha hb s t hs run) 17 s hs

#print axioms preserves
#print axioms all_calls
end NHX_LowDomain
