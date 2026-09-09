import QueriedInverse
import QuotientFold
import SelectedQuotientOriginal

/-! Ordered query arithmetic after canonical parsing/authentication. The
received word is arbitrary. A successful nested-norm checked batch constructs
the actual inverse array; no global liveness, polynomiality or image premise
is used. This is a field/index interface, not a Rust parser/replay translation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 25000
namespace AspisV8.QueriedResidual
noncomputable section
open AspisV5ComponentCQM31TowerExact AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriConcreteEncoderCommutation
open AspisPool.V7C1ConcreteProjectionBinding AspisV7ExactOneFoldDomains
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisK1.V7Tag73CanonicalOneFoldSchedule
open AspisV8.OODInterpolant AspisV8.SelectedQuotientOriginal
open AspisV8.PostQueryFunctional AspisV8.PartialFoldRecovery
abbrev K := QM31Exact
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero

def xs (x : K) : Fin 4 → K := ![x,x,-x,-x]
def ys (y : K) : Fin 4 → K := ![y,-y,-y,y]

theorem stored_slot_x (i : Fin 262144) (j : Fin 4) :
    symbolX (childIndex i j)=xs (exactCircleX i) j := by
  unfold symbolX
  rw [storedInitialCirclePoint20_x_slots]
  fin_cases j <;> simp only [storedCircleSlotX20,xs,exactCircleX,map_neg,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals rfl

theorem stored_slot_y (i : Fin 262144) (j : Fin 4) :
    symbolY (childIndex i j)=ys (exactCircleY i) j := by
  unfold symbolY
  rw [storedInitialCirclePoint20_y_slots]
  fin_cases j <;> simp only [storedCircleSlotY20,ys,exactCircleY,map_neg,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals rfl

def sourceDenom (d : Data (K := K)) (i : Fin 262144) (j : Fin 4) : K :=
  d.a+d.b*xs (exactCircleX i) j+d.c*ys (exactCircleY i) j

theorem sourceDenom_eq (d : Data (K := K)) (i : Fin 262144) (j : Fin 4) :
    sourceDenom d i j=denominator d (childIndex i j) := by
  rw [denominator,stored_slot_x,stored_slot_y]
  rfl

def sourceNumerator (d : Data (K := K)) (received : Fin 1048576 → K)
    (i : Fin 262144) (j : Fin 4) : K :=
  received (childIndex i j)-(d.intercept+d.slope*selected d.useX
    (xs (exactCircleX i) j) (ys (exactCircleY i) j))

theorem sourceNumerator_eq (d : Data (K := K)) (received : Fin 1048576 → K)
    (i : Fin 262144) (j : Fin 4) :
    sourceNumerator d received i j=
      received (childIndex i j)-exactInitialEncoder d.interpolant (childIndex i j) := by
  have hi : exactInitialEncoder d.interpolant (childIndex i j)=
      d.intercept+d.slope*selected d.useX (symbolX (childIndex i j))
        (symbolY (childIndex i j)) :=
    vector_eval d.useX d.intercept d.slope _ _
  rw [hi,stored_slot_x,stored_slot_y]
  rfl

/-- Flat arithmetic storage is 4*queryOrdinal+slot; Merkle authentication's
separately sorted entries do not reorder this array. -/
def denomArray {q : Nat} (d : Data (K := K)) (queries : Fin q → Fin 262144) :
    Fin (4*q) → K :=
  fun k=>sourceDenom d (queries (parentIndex k)) (slotIndex k)
def denominatorList {q : Nat} (d : Data (K := K)) (queries : Fin q → Fin 262144) : List K :=
  List.ofFn (denomArray d queries)

theorem denomArray_child {q : Nat} (d : Data (K := K))
    (queries : Fin q → Fin 262144) (i : Fin q) (j : Fin 4) :
    denomArray d queries (childIndex i j)=denominator d (childIndex (queries i) j) := by
  simp only [denomArray,parentIndex_childIndex,slotIndex_childIndex,sourceDenom_eq]

theorem getD_ofFn {n : Nat} (f : Fin n → K) (i : Fin n) :
    (List.ofFn f).getD i.val 0=f i := by
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt)]
  exact List.getElem_ofFn _

def inverseAt {q : Nat} (out : List K × List M31Exact) (i : Fin q) (j : Fin 4) : K :=
  out.1.getD (childIndex i j).val 0

theorem success_inverse {q : Nat} (d : Data (K := K))
    (queries : Fin q → Fin 262144) (base : List M31Exact) (out : List K × List M31Exact)
    (success : QueriedInverse.checked (denominatorList d queries) base=some out)
    (i : Fin q) (j : Fin 4) :
    inverseAt out i j=(denominator d (childIndex (queries i) j))⁻¹ := by
  have equal := (QueriedInverse.success_values _ _ _ success).2.1
  unfold inverseAt
  rw [equal]
  have hm := List.getD_map (l := denominatorList d queries) (d := (0 : K))
    (n := (childIndex i j).val) (fun v : K=>v⁻¹)
  simp only [inv_zero] at hm
  rw [hm]
  rw [denominatorList,getD_ofFn,denomArray_child]

theorem queried_pole_reject {q : Nat} (d : Data (K := K))
    (queries : Fin q → Fin 262144) (base : List M31Exact)
    (i : Fin q) (j : Fin 4) (pole : denominator d (childIndex (queries i) j)=0) :
    QueriedInverse.checked (denominatorList d queries) base=none := by
  apply QueriedInverse.queried_zero_reject
  apply List.mem_ofFn.mpr
  exact ⟨childIndex i j,(denomArray_child d queries i j).trans pole⟩

theorem queried_pole_fibre_reject {q : Nat} (d : Data (K := K))
    (queries : Fin q → Fin 262144) (base : List M31Exact)
    (i : Fin q) (pole : queries i∈poleFibres d) :
    QueriedInverse.checked (denominatorList d queries) base=none := by
  obtain ⟨symbol,hsame,hparent⟩ := Finset.mem_image.mp pole
  have hz : denominator d symbol=0 := (Finset.mem_filter.mp hsame).2
  apply queried_pole_reject d queries base i (slotIndex symbol)
  rw [← hparent,childIndex_parentIndex_slotIndex]
  exact hz

def sourceSlots {q : Nat} (d : Data (K := K)) (received : Fin 1048576 → K)
    (queries : Fin q → Fin 262144) (out : List K × List M31Exact) (i : Fin q) : Fin 4 → K :=
  fun j=>sourceNumerator d received (queries i) j*inverseAt out i j

theorem success_slots {q : Nat} (d : Data (K := K)) (received : Fin 1048576 → K)
    (queries : Fin q → Fin 262144) (base : List M31Exact) (out : List K × List M31Exact)
    (success : QueriedInverse.checked (denominatorList d queries) base=some out)
    (i : Fin q) :
    sourceSlots d received queries out i=fun j=>virtual d received (childIndex (queries i) j) := by
  funext j
  rw [sourceSlots,sourceNumerator_eq,success_inverse d queries base out success i j]
  rfl

def baseIndex {q : Nat} (i : Fin q) (odd : Bool) : Fin (2*q) :=
  ⟨2*i.val+(if odd then 1 else 0),by cases odd <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega⟩
def baseParent {q : Nat} (i : Fin (2*q)) : Fin q := ⟨i.val/2,by omega⟩
theorem baseParent_index {q : Nat} (i : Fin q) (odd : Bool) :
    baseParent (baseIndex i odd)=i := by
  apply Fin.ext
  cases odd <;> simp only [baseParent,baseIndex,Bool.false_eq_true,ite_false,ite_true]
  all_goals omega

def baseArray {q : Nat} (queries : Fin q → Fin 262144) (i : Fin (2*q)) : M31Exact :=
  let p := storedInitialFibrePoint20 (queries (baseParent i))
  if i.val%2=0 then 2*AspisCircleGroupOrder.X p else 2*p.1.2
def baseList {q : Nat} (queries : Fin q → Fin 262144) : List M31Exact := List.ofFn (baseArray queries)

theorem baseArray_index {q : Nat} (queries : Fin q → Fin 262144) (i : Fin q) (odd : Bool) :
    algebraMap M31Exact K (baseArray queries (baseIndex i odd))=
      if odd then 2*exactCircleY (queries i) else 2*exactCircleX (queries i) := by
  unfold baseArray
  rw [baseParent_index]
  cases odd
  · have hm : (baseIndex i false).val%2=0 := by simp only [baseIndex,Bool.false_eq_true,ite_false]; omega
    simp only [hm,ite_true,Bool.false_eq_true,ite_false,map_mul,map_ofNat,exactCircleX]
    rfl
  · have hm : (baseIndex i true).val%2≠0 := by simp only [baseIndex,ite_true]; omega
    simp only [hm,ite_false,ite_true,map_mul,map_ofNat,exactCircleY]
    rfl

def baseInverseAt {q : Nat} (out : List K × List M31Exact) (i : Fin q) (odd : Bool) : K :=
  algebraMap M31Exact K (out.2.getD (baseIndex i odd).val 0)

theorem success_base_inverse {q : Nat} (d : Data (K := K))
    (queries : Fin q → Fin 262144) (out : List K × List M31Exact)
    (success : QueriedInverse.checked (denominatorList d queries) (baseList queries)=some out)
    (i : Fin q) (odd : Bool) :
    baseInverseAt out i odd=
      (if odd then 2*exactCircleY (queries i) else 2*exactCircleX (queries i))⁻¹ := by
  have equal := (QueriedInverse.success_values _ _ _ success).2.2
  unfold baseInverseAt
  rw [equal]
  have hm := List.getD_map (l := baseList queries) (d := (0 : M31Exact))
    (n := (baseIndex i odd).val) (fun v : M31Exact=>v⁻¹)
  simp only [inv_zero] at hm
  rw [hm,baseList,List.getD_eq_getElem _ _ (by
    simpa only [List.length_ofFn] using (baseIndex i odd).isLt)]
  simp only [List.getElem_ofFn,map_inv₀]
  rw [baseArray_index]

section Fused
variable {F : Type*} [Field F]
theorem fused_circle (alpha ix iy : F) (v : Fin 4 → F) :
    QuotientFold.expanded (1/2) alpha ix iy (v 0) (v 1) (v 2) (v 3)=
      circleFoldValue alpha ix iy v := by
  rw [QuotientFold.fold_identity]
  unfold QuotientFold.sequential circleFoldValue lineFoldValue pairFoldValue
  simp only [div_eq_mul_inv]
  ring
end Fused

def sourceFold {q : Nat} (d : Data (K := K)) (received : Fin 1048576 → K)
    (queries : Fin q → Fin 262144) (out : List K × List M31Exact) (alpha : K) (i : Fin q) : K :=
  let v := sourceSlots d received queries out i
  QuotientFold.expanded (1/2) alpha (baseInverseAt out i false)
    (baseInverseAt out i true) (v 0) (v 1) (v 2) (v 3)

theorem success_fold {q : Nat} (d : Data (K := K)) (received : Fin 1048576 → K)
    (queries : Fin q → Fin 262144) (out : List K × List M31Exact)
    (success : QueriedInverse.checked (denominatorList d queries) (baseList queries)=some out)
    (alpha : K) (i : Fin q) :
    sourceFold d received queries out alpha i=
      (SelectedReceivedOracle.oracle (0 : Fin 1024 → K) (virtual d received)).folded alpha
        (storedPoint (K := K) (queries i)) := by
  unfold sourceFold
  rw [fused_circle,success_slots d received queries (baseList queries) out success i,
    success_base_inverse d queries out success i false,success_base_inverse d queries out success i true]
  simp only [CausalOrderedRelation.FixedOracle.folded,SelectedReceivedOracle.oracle,
    SelectedReceivedOracle.index_point,Bool.false_eq_true,ite_false,ite_true]

theorem success_residual {q : Nat} (d : Data (K := K)) (received : Fin 1048576 → K)
    (queries : Fin q → Fin 262144) (out : List K × List M31Exact)
    (success : QueriedInverse.checked (denominatorList d queries) (baseList queries)=some out)
    (alpha : K) (final : Fin 256 → K) (i : Fin q) :
    exactFinalLinear final (queries i)-sourceFold d received queries out alpha i=
      PostQueryFunctional.residual final (fun j=>storedPoint (K := K) (queries j))
        ((SelectedReceivedOracle.oracle (0 : Fin 1024 → K) (virtual d received)).folded alpha) i := by
  rw [success_fold d received queries out success alpha i]
  simp only [PostQueryFunctional.residual,SelectedReceivedOracle.final_evaluation]

#print axioms stored_slot_x
#print axioms stored_slot_y
#print axioms sourceNumerator_eq
#print axioms success_inverse
#print axioms queried_pole_reject
#print axioms queried_pole_fibre_reject
#print axioms success_slots
#print axioms success_base_inverse
#print axioms fused_circle
#print axioms success_fold
#print axioms success_residual
end
end AspisV8.QueriedResidual
