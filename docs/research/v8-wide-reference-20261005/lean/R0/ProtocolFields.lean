import R0.Binding

/-! The field-of-definition specialization for the protocol's 26 base-field
lanes and three QM31 lanes. -/
set_option autoImplicit false
namespace AspisR0.Opening
open AspisWideTower AspisV5ComponentCQM31TowerExact AspisCircleGroupOrder
noncomputable section
local instance : DecidableEq WideExact := Classical.decEq _

def protocolField (l : Fin 29) : Subfield WideExact :=
  if l.val < 26 then (algebraMap (ZMod AspisCircleGroupOrder.P) WideExact).fieldRange
  else (algebraMap QM31Exact WideExact).fieldRange

theorem protocolField_base (l : Fin 29) (hl : l.val < 26) (x : WideExact) :
    x ∈ protocolField l ↔ x ∈ Set.range (algebraMap (ZMod AspisCircleGroupOrder.P) WideExact) := by
  simp only [protocolField, if_pos hl, RingHom.mem_fieldRange, Set.mem_range]

theorem protocolField_qm31 (l : Fin 29) (hl : 26 ≤ l.val) (x : WideExact) :
    x ∈ protocolField l ↔ x ∈ Set.range (algebraMap QM31Exact WideExact) := by
  simp only [protocolField, if_neg (Nat.not_lt.mpr hl), RingHom.mem_fieldRange, Set.mem_range]

theorem wideProtocolBinding (D : Data WideExact) (hne : D.z0 ≠ D.z1)
    (h0 : ¬ Chord.BaseRational D.z0) (h1 : ¬ Chord.BaseRational D.z1)
    (base : ∀ l i, D.W l i ∈ protocolField l) :
    type_of% (binding D hne h0 h1 protocolField base) :=
  binding D hne h0 h1 protocolField base

#print axioms protocolField_base
#print axioms protocolField_qm31
#print axioms wideProtocolBinding
end
end AspisR0.Opening
