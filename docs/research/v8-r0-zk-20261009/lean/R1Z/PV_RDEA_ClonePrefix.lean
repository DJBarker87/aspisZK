import R1Z.PV_RDEA_ExecutionHeaders
import R1Z.PV_RDEA_PrefixWords
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEA_ClonePrefix
open PV_RDB1_V183_ReserveWorld PV_RDEA_CapacityEndpoint PV_RDEA_PrefixWords

theorem success_bounds {S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (address n : Nat) (w : World S F)
    (success : (PV_RDB1_V181.deployed step wordMax byteMax shape address n w).returned=.ok ()) :
    n≤wordMax ∧ n*shape.width≤byteMax := by
  have hw : n≤wordMax := by
    by_contra hn
    have h : n>wordMax := by omega
    simp only [PV_RDB1_V181.deployed,h,ite_true] at success
    cases success
  refine ⟨hw,?_⟩
  by_contra hn
  have hb : n*shape.width>byteMax := by omega
  have h : ¬n>wordMax := by omega
  simp only [PV_RDB1_V181.deployed,h,hb,ite_false,ite_true] at success
  cases success

theorem clone_requests_prefix {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (address : Nat)
    (base : List U8) (w : World S F) :
    Prefix (sizes (PV_RDEA_CloneExecution.clone step shape address base w).2.history)
      (sizes w.history++cloneWord base.length) := by
  rw [PV_RDEA_CloneExecution.clone_sizes step shape width]
  exact left _ _ _ (constructor_prefix _)

#print axioms success_bounds
#print axioms clone_requests_prefix
end R1Z.PV_RDEA_ClonePrefix
