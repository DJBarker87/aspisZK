import PV_B1_Close254
import PV_B1_Close230
import PV_B1_PoleWitnesses
set_option autoImplicit false
noncomputable section
namespace PV_B1_Nonvacuity
open Aeneas Aeneas.Std Result ProverRwFull PV_B1_ActualInstall
-- Logical satisfiability only. These callbacks are NEVER used as a native model,
-- executable reference, or a replacement for any non-target source obligation.
def opaqueTypes : ExternalTypes := by
  constructor <;> intros <;> exact Unit

def fallback [ExternalTypes] : ExternalFuns := by
  constructor <;> intros <;> exact fail .panic

theorem callback_type_inhabited [ExternalTypes] : Nonempty ExternalFuns := ⟨fallback⟩
local instance sampleTypes : ExternalTypes := opaqueTypes
def ops : ExternalFuns := fallback
def q : HQ := {c0:={a:=0#u32,b:=0#u32},c1:={a:=0#u32,b:=0#u32}}
def w : HW := PV_B1_ActualCarrierWide.fromW PV_B1_254.aspis_core.field.wide_exact.WideExact.ZERO
def row : Array (Array HQ 2#usize) 2#usize := Array.repeat 2#usize (Array.repeat 2#usize q)

theorem joint_success :
    (∃ out : Array HW 1#usize, (selected ops).op254 1#usize w=ok out) ∧
    (∃ y, (selected ops).op230 (⟨List.replicate 1024 q,by simp only [List.length_replicate]; scalar_tac⟩ : Slice HQ)=ok (some y)) ∧
    (∃ b, (selected ops).op258 (⟨[row],by simp only [List.length_cons,List.length_nil]; scalar_tac⟩ : Rows)
      (Array.repeat 64#usize 0#u16) q=ok b) :=
  ⟨PV_B1_Close254.nonvacuity ops w,PV_B1_Close230.nonvacuity ops q,
    PV_B1_PoleWitnesses.nonempty ops _ q row⟩
#print axioms opaqueTypes
#print axioms fallback
#print axioms callback_type_inhabited
#print axioms joint_success
end PV_B1_Nonvacuity
