import R1Z.PV_Inv_PackList
import R1Z.PoleMassR1
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_ModelRow
open R0P R0Z.HonestValidity PV_Inv_Pack PV_Inv_PackList
variable {K : Type} [Field K] [DecidableEq K]

def entries (t : Trace K) (lam : K) (b : Fin 1024)
    (side : CopyLink → CopyEndpoint) (weights : Fin 2 → K) : List (Endpoint K) :=
  List.ofFn (fun s : Fin 2 => ⟨copyRowValues t lam b side s,weights s⟩)

theorem producer_clear (t : Trace K) (lam chi : K) (b : Fin 1024) (active : CopyActiveRow b)
    (weights : Fin 2 → K) (hp : NoPole t lam chi) :
    ∀ e ∈ entries t lam b CopyLink.producer weights, chi ≠ e.value := by
  intro e he
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp he
  subst e
  exact (hp b active i).1

theorem consumer_clear (t : Trace K) (lam chi : K) (b : Fin 1024) (active : CopyActiveRow b)
    (weights : Fin 2 → K) (hp : NoPole t lam chi) :
    ∀ e ∈ entries t lam b CopyLink.consumer weights, chi ≠ e.value := by
  intro e he
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp he
  subst e
  exact (hp b active i).2

#print axioms producer_clear
#print axioms consumer_clear
end R1Z.PV_Inv_ModelRow
