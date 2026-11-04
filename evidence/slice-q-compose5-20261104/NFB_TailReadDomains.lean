import NFB_TailDefs
set_option autoImplicit false
noncomputable section
namespace NFB_TailReadDomains
open Aeneas Aeneas.Std Result AspisR1 NFB_TailProgram

theorem first (q : Array U8 608#usize) (g : Coeff) (slot : Usize)
 (canonical : NEV_DotInputs.Canonical g) (e : E) (scalar : Q)
 (accepted : NFB_TailProgram.first q g slot=ok (e,scalar)) :
 NEV_DotCarrier.canonE e ∧ NEV_DotCarrier.canonQ scalar := by
 unfold NFB_TailProgram.first at accepted
 obtain ⟨actual,select,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
 obtain ⟨base,_,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
 obtain ⟨start,_,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
 obtain ⟨stop,_,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
 obtain ⟨value,read,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
 have same : (actual,value)=(e,scalar) := Result.ok.inj accepted
 cases same
 exact ⟨NEV_DotInputs.selected g canonical 28#usize (by decide) e select,
  NFA_TailQM.source q start stop scalar read⟩

theorem later (q : Array U8 608#usize) (g : Coeff) (stride position : Usize)
 (canonical : NEV_DotInputs.Canonical g) (small : position.val<2) (e : E) (scalar : Q)
 (accepted : NFB_TailProgram.later q g stride position=ok (e,scalar)) :
 NEV_DotCarrier.canonE e ∧ NEV_DotCarrier.canonQ scalar := by
 unfold NFB_TailProgram.later at accepted
 obtain ⟨base,_,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
 obtain ⟨delta,_,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
 obtain ⟨start,_,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
 obtain ⟨index,indexRun,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
 obtain ⟨actual,select,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
 obtain ⟨stop,_,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
 obtain ⟨value,read,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
 have same : (actual,value)=(e,scalar) := Result.ok.inj accepted
 cases same
 have indexVal : index.val=position.val+26 := by
  obtain ⟨j,run,value⟩ := WP.spec_imp_exists
   (UScalar.add_spec (x:=position) (y:=26#usize) (by scalar_tac))
  have sameIndex : j=index := Result.ok.inj (run.symm.trans indexRun)
  subst j
  exact value
 exact ⟨NEV_DotInputs.selected g canonical index (by omega) e select,
  NFA_TailQM.source q start stop scalar read⟩
#print axioms first
#print axioms later
end NFB_TailReadDomains
end
