import R1Z.PV_OWNC_PushValid
set_option autoImplicit false
namespace R1Z.PV_OWNC_PushFold
open PV_OWNC_Vector PV_OWN_View
/-- Consecutive initialized stores, each publishing len after its own write. -/
def append {T : Type} (k : Codec T) : Buffer T → List T → Buffer T
 | b,[] => b
 | b,v::vs => append k (push k b v (k.encode v)) vs

theorem length {T : Type} (k : Codec T) (b : Buffer T) (xs : List T) :
 (append k b xs).length=b.length+xs.length := by
 induction xs generalizing b with
 | nil => simp only [append,List.length_nil,Nat.add_zero]
 | cons v vs ih =>
  rw [append,ih]
  change b.length+1+vs.length=b.length+(vs.length+1)
  omega

theorem capacity {T : Type} (k : Codec T) (b : Buffer T) (xs : List T) :
 (append k b xs).capacity=b.capacity := by
 induction xs generalizing b with
 | nil => rfl
 | cons v vs ih => exact ih _

theorem valid {T : Type} (k : Codec T) (b : Buffer T) (xs : List T)
 (h:Valid k b) (room:b.length+xs.length≤b.capacity)
 (bounded:∀ x i z, k.encode x i=some z → i<k.width) :
 Valid k (append k b xs) := by
 induction xs generalizing b with
 | nil => exact h
 | cons v vs ih =>
  apply ih
  · exact PV_OWNC_PushValid.valid k b v _ h (by simp only [List.length_cons] at room;omega)
     bounded (PV_OWNB_Padding.refl _)
  · change b.length+1+vs.length≤b.capacity
    simp only [List.length_cons] at room
    omega
attribute [local irreducible] append
#print axioms length
#print axioms capacity
#print axioms valid
end R1Z.PV_OWNC_PushFold
