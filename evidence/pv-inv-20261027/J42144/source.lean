import R1Z.PV_Inv_ModelRow
import R1Z.PV_Inv_PackOperands
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_ModelPack
open R0P R0Z.HonestValidity PV_Inv_Pack PV_Inv_PackList PV_Inv_PackOperands PV_Inv_ModelRow
variable {K : Type} [Field K] [DecidableEq K]

theorem producer (t : Trace K) (lam chi : K) (b : Fin 1024) (active : CopyActiveRow b)
    (weights : Fin 2 → K) (hp : NoPole t lam chi) (s : Slots K)
    (run : PV_Inv_PackList.run empty (entries t lam b CopyLink.producer weights) = some s) :
    ∀ d ∈ operands chi s, d ≠ 0 :=
  packed_nonzero chi _ s (producer_clear t lam chi b active weights hp) run

theorem consumer (t : Trace K) (lam chi : K) (b : Fin 1024) (active : CopyActiveRow b)
    (weights : Fin 2 → K) (hp : NoPole t lam chi) (s : Slots K)
    (run : PV_Inv_PackList.run empty (entries t lam b CopyLink.consumer weights) = some s) :
    ∀ d ∈ operands chi s, d ≠ 0 :=
  packed_nonzero chi _ s (consumer_clear t lam chi b active weights hp) run

#print axioms producer
#print axioms consumer
end R1Z.PV_Inv_ModelPack
