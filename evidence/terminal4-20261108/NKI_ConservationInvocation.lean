import NKI_ValueFinish
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_ConservationInvocation
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open NKI_ValuePrefix (Openings Selectors)
open pool_v1.pair_forest_semantic_terminal
structure Locals where
 i2 : Usize
 i3 : Usize
 conservation_selector : NQ
 q15 : NQ
 q16 : NQ
 q17 : NQ
 q18 : NQ
 q19 : NQ
 q20 : NQ
 q21 : NQ
 q22 : NQ
 q23 : NQ
 q24 : NQ
def Clauses (packed : Array NQ 24#usize) (o : Openings) (s : Selectors) (out : Array NQ 24#usize) (l : Locals) : Prop :=
 let i2:=l.i2
 let i3:=l.i3
 let conservation_selector:=l.conservation_selector
 let q15:=l.q15
 let q16:=l.q16
 let q17:=l.q17
 let q18:=l.q18
 let q19:=l.q19
 let q20:=l.q20
 let q21:=l.q21
 let q22:=l.q22
 let q23:=l.q23
 let q24:=l.q24
 (16#usize * VALUE_AUXILIARY_BLOCK=ok i2) ∧
 (i2 + 6#usize=ok i3) ∧
 (pool_v1.pair_forest_copy_terminal.Selectors.row s i3=ok conservation_selector) ∧
 (Array.index_usize o.z 0#usize=ok q15) ∧
 (Array.index_usize o.z 1#usize=ok q16) ∧
 (field.QM31.sub q15 q16=ok q17) ∧
 (Array.index_usize o.z 2#usize=ok q18) ∧
 (field.QM31.sub q17 q18=ok q19) ∧
 (field.QM31.mul conservation_selector q19=ok q20) ∧
 (Array.index_usize o.succ_z 0#usize=ok q21) ∧
 (Array.index_usize o.succ_z 1#usize=ok q22) ∧
 (field.QM31.sub q21 q22=ok q23) ∧
 (field.QM31.mul conservation_selector q23=ok q24) ∧
 (add_preweighted packed 82#usize (Array.make 2#usize [q20,q24])=ok out)
theorem source (packed : Array NQ 24#usize) (o : Openings) (s : Selectors) (out : Array NQ 24#usize)
 (run : NKI_ValueFinish.conservation packed o s=ok out) : ∃ l,Clauses packed o s out l := by
 unfold NKI_ValueFinish.conservation at run
 obtain ⟨i2,c0,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨i3,c1,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨conservation_selector,c2,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q15,c3,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q16,c4,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q17,c5,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q18,c6,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q19,c7,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q20,c8,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q21,c9,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q22,c10,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q23,c11,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q24,c12,run⟩ := FIv_Map.bind_success _ _ _ run
 exact ⟨⟨i2,i3,conservation_selector,q15,q16,q17,q18,q19,q20,q21,q22,q23,q24⟩,⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,run⟩⟩
#print axioms source
end AspisR1.NKI_ConservationInvocation
end
