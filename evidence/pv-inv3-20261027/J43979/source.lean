import R1Z.PV_Inv_GuardSites
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_GuardAllSites
open R0P R0Z.HonestValidity PV_Inv_GuardSites
variable {K : Type} [Field K] [DecidableEq K]
attribute [local irreducible] copyLinks copyPatterns copyActiveRowMasks copyInactiveRows

def active : List (Fin 1024) :=
  (List.ofFn (fun b : Fin 1024 => b)).filter (fun b => decide (CopyActiveRow b))
def sites (t : Trace K) (lambda : K) : List K := active.flatMap (rowSites t lambda)

theorem active_mem (b : Fin 1024) : b ∈ active ↔ CopyActiveRow b := by
  simp only [active,List.mem_filter,List.mem_ofFn,exists_eq,true_and,decide_eq_true_eq]

theorem sites_clear (t : Trace K) (lambda chi : K) :
    (∀ v ∈ sites t lambda, chi ≠ v) ↔ NoPole t lambda chi := by
  constructor
  · intro h b hb
    apply (row_clear t lambda chi b).mp
    intro v hv
    exact h v (List.mem_flatMap.mpr ⟨b,(active_mem b).mpr hb,hv⟩)
  · intro h v hv
    obtain ⟨b,hb,hv⟩ := List.mem_flatMap.mp hv
    exact (row_clear t lambda chi b).mpr (h b ((active_mem b).mp hb)) v hv

#print axioms active_mem
#print axioms sites_clear
end R1Z.PV_Inv_GuardAllSites
