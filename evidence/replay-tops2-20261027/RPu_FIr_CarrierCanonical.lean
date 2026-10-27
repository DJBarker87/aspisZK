import RPu_FIr_GatherCanonical
import RPu_FIq_Carriers
import RPt_FIp_SemanticValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_CarrierCanonical
open Aeneas Aeneas.Std Result
open FIq_Carriers

theorem to_canon (x : MQ) : FIr_NativeValue.Canon (toQ x) ↔ FIp_SemanticValues.Canon x := Iff.rfl

theorem to_value (x : MQ) : FIr_NativeValue.decode (toQ x)=FIp_SemanticValues.decode x := rfl

theorem from_canon (x : NQ) : FIp_SemanticValues.Canon (fromQ x) ↔ FIr_NativeValue.Canon x := Iff.rfl

theorem from_value (x : NQ) : FIp_SemanticValues.decode (fromQ x)=FIr_NativeValue.decode x := rfl

theorem array {N : Usize} (a : Array MQ N) (all : ∀ x∈a.val,FIp_SemanticValues.Canon x) :
    ∀ x∈(mapArray toQ a).val,FIr_NativeValue.Canon x := by
  intro x mem
  obtain ⟨y,member,rfl⟩ := List.mem_map.mp mem
  exact (to_canon y).mpr (all y member)

theorem claims (a : Array (Array MQ 29#usize) 3#usize)
    (all : ∀ row∈a.val,∀ x∈row.val,FIp_SemanticValues.Canon x) :
    FIr_GatherCallback.CanonClaims (mapArray (mapArray toQ) a) := by
  intro row member
  obtain ⟨r,mem,rfl⟩ := List.mem_map.mp member
  exact array r (all r mem)

#print axioms to_canon
#print axioms to_value
#print axioms from_canon
#print axioms from_value
#print axioms array
#print axioms claims
end AspisR1.FIr_CarrierCanonical
end
