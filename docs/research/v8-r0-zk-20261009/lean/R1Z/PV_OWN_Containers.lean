import R1Z.PV_OWN_U8
import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Containers
open PV_OWN_Heap PV_OWN_View PV_OWN_Operations
/-- Public Vec relation separates zero-capacity, allocation-free storage from
an allocated Vec. The internal Operations.VecView describes allocated storage. -/
def VecView {T : Type} (codec : Codec T) (m : Memory) (v : Vector T) : Prop :=
 (v.capacity=0 ∧ v.values=[] ∧ m.slots v.owner=none) ∨
 (v.capacity>0 ∧ PV_OWN_Operations.VecView codec m v)

/-- UTF8 is an encoding relation, not a caller-selectable predicate. -/
def StringView (m : Memory) (v : Vector UInt8) : Prop :=
 VecView PV_OWN_U8.codec m v ∧ ∃ text : String, text.toUTF8.data.toList=v.values

theorem zero_capacity {T : Type} (codec : Codec T) (m : Memory) (v : Vector T)
 (h:VecView codec m v) (zero:v.capacity=0) : v.values=[] ∧ m.slots v.owner=none := by
 cases h with
 | inl h => exact h.2
 | inr h => have hh:=h.1; omega

theorem allocated {T : Type} (codec : Codec T) (m : Memory) (v : Vector T)
 (h:VecView codec m v) (positive:v.capacity>0) : PV_OWN_Operations.VecView codec m v := by
 cases h with
 | inl h => have hh:=h.1; omega
 | inr h => exact h.2

theorem utf8 (m : Memory) (v : Vector UInt8) (h:StringView m v) :
 ∃ text : String, text.toUTF8.data.toList=v.values := h.2
#print axioms zero_capacity
#print axioms allocated
#print axioms utf8
end R1Z.PV_OWN_Containers
