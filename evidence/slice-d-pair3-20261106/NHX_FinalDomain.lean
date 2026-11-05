import NHX_FinalLoop
import NHX_FieldResults
set_option autoImplicit false
namespace NHX_FinalDomain
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues
open NHX_FinalLoop

theorem preserves (parts powers : Cells)
 (hp:∀ x∈parts.val,canonE x) (hk:∀ x∈powers.val,canonE x)
 (s t:State) (hs:canonE s.2) (run:body parts powers s=ok (.cont t)) : canonE t.2 := by
 unfold body at run
 obtain ⟨⟨o,next⟩,hn,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 cases o with
 | none=>cases run
 | some i=>
  obtain ⟨part,hpart,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨power,hpower,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨sum,hsum,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  have cp:=NHM_ArrayCanon.read canonE parts i part hp hpart
  have ck:=NHM_ArrayCanon.read canonE powers i power hk hpower
  obtain ⟨out,ho,co⟩:=NHX_FinalFold.cell_total s.2 power part hs ck cp
  rw [hsum] at ho
  cases Result.ok.inj ho
  have same:=ControlFlow.cont.inj (Result.ok.inj run)
  rw [←same]
  exact co

/-- Every reached final-fold state uses the SAME canonical accumulator; the
array operands are immutable and indexed by the actual loop iterator. -/
theorem all_calls (parts powers:Cells) (hp:∀ x∈parts.val,canonE x)
 (hk:∀ x∈powers.val,canonE x) : NHM_LoopDomain.all (body parts powers)
 (fun s=>canonE s.2) 8 ({start:=0#usize,«end»:=7#usize},NHI_Scalar.zero) :=
 NHM_LoopDomain.invariant (body parts powers) (fun s=>canonE s.2)
 (fun s t hs run=>preserves parts powers hp hk s t hs run) 8 _ NHI_Scalar.zero_canonical

/-- SAME kappa, not an independently selected seven-power witness. -/
theorem from_kappa (parts:Cells) (hp:∀ x∈parts.val,canonE x) (kappa:NE) (hc:canonE kappa) :
 ∃ powers:Cells,FIo_Native.weights.powers 7#usize kappa=ok powers ∧
 NHM_LoopDomain.all (body parts powers) (fun s=>canonE s.2) 8
 ({start:=0#usize,«end»:=7#usize},NHI_Scalar.zero) := by
 obtain ⟨powers,run,hk⟩:=NHX_Powers7Edge.source kappa hc
 exact ⟨powers,run,all_calls parts powers hp hk⟩

#print axioms preserves
#print axioms all_calls
#print axioms from_kappa
end NHX_FinalDomain
