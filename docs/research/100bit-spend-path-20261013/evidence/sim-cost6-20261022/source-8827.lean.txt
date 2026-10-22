import R1Z.SimCostFormula5

/-! Explicit payload-cell indexing without derived Fintype enumeration.
These are value/representation laws. They do not assign a zero cost to
materialization, index computation, serialization or evaluation of a closure. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.SimCostRepresentation6
open R0Z.HonestView R1Z.Batched R1Z.SimCostFormula5 AspisWideTower

def unitIndex : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv u := by cases u; rfl
  right_inv i := Subsingleton.elim _ _

def sumIndex {A B : Type} {n m : Nat} (a : A ≃ Fin n) (b : B ≃ Fin m) :
    A ⊕ B ≃ Fin (n+m) := (Equiv.sumCongr a b).trans finSumFinEquiv

def prodIndex {A B : Type} {n m : Nat} (a : A ≃ Fin n) (b : B ≃ Fin m) :
    A × B ≃ Fin (n*m) := (Equiv.prodCongr a b).trans finProdFinEquiv

def batIndex : R1Bat ≃ Fin 262222 := R1Bat.equivSum.trans
  (sumIndex (sumIndex (Equiv.refl _) (Equiv.refl _))
    (sumIndex (Equiv.refl _) (Equiv.refl _)))

/-- Eight actual constructor blocks, using arithmetic sum/product indexing. -/
def index : PayloadCell R1Bat ≃ Fin 30671382 := payloadEquiv.trans
  (sumIndex unitIndex
    (sumIndex (prodIndex (Equiv.refl _) (Equiv.refl _))
      (sumIndex (prodIndex (Equiv.refl _) (Equiv.refl _))
        (sumIndex (Equiv.refl _)
          (sumIndex (prodIndex (Equiv.refl _) (Equiv.refl _))
            (sumIndex unitIndex
              (sumIndex (prodIndex (Equiv.refl _)
                (prodIndex (Equiv.refl _) (Equiv.refl _))) batIndex)))))))

def encode {K : Type} (v : Payload K R1Bat) : Fin 30671382 → K :=
  fun i => v (index.symm i)

def decode {K : Type} (a : Fin 30671382 → K) : Payload K R1Bat :=
  fun c => a (index c)

theorem decode_encode {K : Type} (v : Payload K R1Bat) : decode (encode v) = v := by
  funext c
  exact congrArg v (index.symm_apply_apply c)

theorem encode_decode {K : Type} (a : Fin 30671382 → K) : encode (decode a) = a := by
  funext i
  exact congrArg a (index.apply_symm_apply i)

/-- The pass-5 algorithm now has an explicit relation to the actual payload
carrier. Its inputs are supplied arrays; this law does not charge encoding. -/
theorem arrayAdd_payload (a b : Fin 30671382 → WideExact) :
    decode (arrayAdd 30671382 (a,b)).1 = decode a + decode b := by
  rw [arrayAdd_erase]
  rfl

theorem payload_add_correct (a b : Payload WideExact R1Bat) :
    decode (arrayAdd 30671382 (encode a,encode b)).1 = a+b := by
  rw [arrayAdd_payload, decode_encode, decode_encode]

#print axioms index
#print axioms decode_encode
#print axioms encode_decode
#print axioms arrayAdd_payload
#print axioms payload_add_correct
end R1Z.SimCostRepresentation6
