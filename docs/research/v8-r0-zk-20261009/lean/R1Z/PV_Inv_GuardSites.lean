import R1Z.PoleMassR1
import R1Z.PV_Inv_Scan
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_GuardSites
open R0P R0Z.HonestValidity
variable {K : Type} [Field K] [DecidableEq K]
attribute [local irreducible] copyLinks copyPatterns copyActiveRowMasks copyInactiveRows

def rowSites (t : Trace K) (lambda : K) (b : Fin 1024) : List K :=
  (List.ofFn (fun s : Fin 2 => copyRowValues t lambda b CopyLink.producer s)) ++
  (List.ofFn (fun s : Fin 2 => copyRowValues t lambda b CopyLink.consumer s))

theorem mem_producer (t : Trace K) (lambda : K) (b : Fin 1024) (s : Fin 2) :
    copyRowValues t lambda b CopyLink.producer s ∈ rowSites t lambda b := by
  exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨s,rfl⟩)

theorem mem_consumer (t : Trace K) (lambda : K) (b : Fin 1024) (s : Fin 2) :
    copyRowValues t lambda b CopyLink.consumer s ∈ rowSites t lambda b := by
  exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨s,rfl⟩)

theorem row_clear (t : Trace K) (lambda chi : K) (b : Fin 1024) :
    (∀ v ∈ rowSites t lambda b, chi ≠ v) ↔
    ∀ s : Fin 2, chi ≠ copyRowValues t lambda b CopyLink.producer s ∧
      chi ≠ copyRowValues t lambda b CopyLink.consumer s := by
  constructor
  · intro h s
    exact ⟨h _ (mem_producer t lambda b s),h _ (mem_consumer t lambda b s)⟩
  · intro h v hv
    rcases List.mem_append.mp hv with hp|hc
    · obtain ⟨s,rfl⟩ := List.mem_ofFn.mp hp
      exact (h s).1
    · obtain ⟨s,rfl⟩ := List.mem_ofFn.mp hc
      exact (h s).2

#print axioms mem_producer
#print axioms mem_consumer
#print axioms row_clear
end R1Z.PV_Inv_GuardSites
