import FourDotsPushProductTraceRootV1
import AspisV8R17.QM31WordTower
import S4TailWideAddCurrentV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsTailFieldProductRootV1
open AspisR1FastDotsPushProductTraceRootV1
abbrev TowerQ := AspisV8R17.QM31WordTower.Q
abbrev TowerWide := AspisWideTower.WideExact

def tupleToTowerQ (t : T) : TowerQ :=
  AspisV8R17.QM31WordTower.embedQ ((t.1,t.2.1),(t.2.2.1,t.2.2.2))

def decodeState (s : S) : TowerWide := ⟨tupleToTowerQ s.1,tupleToTowerQ s.2⟩

def qmDecoded (q : QM) : TowerQ :=
  AspisV8R17.QM31WordTower.decodeQ
    ((q.c0.a.val,q.c0.b.val),(q.c1.a.val,q.c1.b.val))

def wideDecoded (x : Wide) : TowerWide := ⟨qmDecoded x.c0,qmDecoded x.c1⟩

def scalarProduct (p : Wide × QM) : TowerWide :=
  ⟨qmDecoded p.1.c0 * qmDecoded p.2,qmDecoded p.1.c1 * qmDecoded p.2⟩

def productSum : List (Wide × QM) → TowerWide
  | [] => 0
  | p::ps => scalarProduct p + productSum ps

/-- Literal specialization of the existing S5 residue-to-tower product
identity; only the current S4 operand carrier replaces the finish carrier. -/
theorem tupleToTowerQ_qmul (x y : AspisV8R17.QM31WordResidues.Q) :
    tupleToTowerQ (AspisR1.R22RawQmProductResidues.qmulCoefficients x y) =
      AspisV8R17.QM31WordTower.embedQ (AspisV8R17.QM31WordResidues.qMul x y) := rfl

theorem low_product_decodes (x : Wide) (q : QM) :
    tupleToTowerQ (lowProduct x q) = qmDecoded x.c0 * qmDecoded q := by
  unfold lowProduct
  rw [tupleToTowerQ_qmul, AspisV8R17.QM31WordTower.embed_product,
    AspisV8R17.QuadraticTowerOperations.qmul_eq]
  rfl

theorem high_product_decodes (x : Wide) (q : QM) :
    tupleToTowerQ (highProduct x q) = qmDecoded x.c1 * qmDecoded q := by
  unfold highProduct
  rw [tupleToTowerQ_qmul, AspisV8R17.QM31WordTower.embed_product,
    AspisV8R17.QuadraticTowerOperations.qmul_eq]
  rfl

theorem tupleToTowerQ_add (x y : T) :
    tupleToTowerQ (AspisR1EbyKPushDecodedProductUpdate.tupleAdd x y) =
      tupleToTowerQ x + tupleToTowerQ y := rfl

theorem decode_addProduct (s : S) (p : Wide × QM) :
    decodeState (addProduct s p) = decodeState s + scalarProduct p := by
  unfold addProduct decodeState scalarProduct
  rw [tupleToTowerQ_add,tupleToTowerQ_add,low_product_decodes,high_product_decodes]
  rfl

theorem decode_product_fold (ps : List (Wide × QM)) (s : S) :
    decodeState (ps.foldl addProduct s) = decodeState s + productSum ps := by
  induction ps generalizing s with
  | nil => simp only [List.foldl_nil,productSum,add_zero]
  | cons p ps ih =>
    rw [List.foldl_cons,ih,decode_addProduct,productSum,add_assoc]

theorem decode_zero_state :
    decodeState (stateValue EbyKNewToPushStateABI.pushZero) = 0 := rfl

theorem current_decode_eq (x : Wide) :
    AspisR1CurrentWide.Proof.decodeWide
      (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x) = wideDecoded x := rfl

/-- Converts exactly the ordered product-state equation already returned by
one successful callback; no raw success or intermediate range premise added. -/
theorem decoded_tail_product_sum (out : State) (ps : List (Wide × QM))
    (h : stateValue out = ps.foldl addProduct
      (stateValue EbyKNewToPushStateABI.pushZero)) :
    decodeState (stateValue out) = productSum ps := by
  rw [h,decode_product_fold,decode_zero_state,zero_add]

#print axioms low_product_decodes
#print axioms high_product_decodes
#print axioms decode_addProduct
#print axioms decode_product_fold
#print axioms current_decode_eq
#print axioms decoded_tail_product_sum
end AspisR1FastDotsTailFieldProductRootV1
