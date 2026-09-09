import LineNormBuffer
import QueriedResidual

/-! Selected query-index to ordered norm-buffer interface. The actual stored
circle points construct their unit proofs; denominator/base list equalities
are derived by symbolic block flattening. This does not translate the Rust
lookup tables, parser, mutable Vec storage, or Merkle authentication. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 30000
namespace AspisV8.SelectedQueryBuffer
noncomputable section
open AspisV5ComponentCQM31TowerExact AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriConcreteEncoderCommutation AspisV7ExactOneFoldDomains
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisV8.OODInterpolant AspisV8.QueriedResidual
open AspisV8.PartialFoldRecovery
open AspisV8.PostQueryFunctional

abbrev K := QM31Exact

/-- The same slot-zero stored circle point used by exactCircleX/Y. -/
def point (i : Fin 262144) : LineNormBuffer.Point :=
  ⟨(storedInitialFibrePoint20 i).val,(storedInitialFibrePoint20 i).property⟩

def points {q : Nat} (queries : Fin q → Fin 262144) : List LineNormBuffer.Point :=
  List.ofFn fun i=>point (queries i)

theorem point_x (i : Fin 262144) :
    algebraMap M31Exact K (point i).val.1=exactCircleX i := rfl
theorem point_y (i : Fin 262144) :
    algebraMap M31Exact K (point i).val.2=exactCircleY i := rfl

theorem point_nonzero (i : Fin 262144) :
    (point i).val.1≠0 ∧ (point i).val.2≠0 := by
  constructor
  · intro h
    apply SelectedReceivedOracle.x_nonzero i
    rw [← point_x,h,map_zero]
  · intro h
    apply SelectedReceivedOracle.y_nonzero i
    rw [← point_y,h,map_zero]

/-- Actual mixed multiplication in the exact tower, not a supplied equality. -/
theorem scale_eq_mul (v : K) (x : M31Exact) :
    LineNormBuffer.scale v x=v*algebraMap M31Exact K x := by
  rw [IsScalarTower.algebraMap_apply M31Exact CM31Exact K x]
  ext <;> simp only [LineNormBuffer.scale,QuadraticAlgebra.re_mul,
    QuadraticAlgebra.im_mul,QuadraticAlgebra.algebraMap_re,
    QuadraticAlgebra.algebraMap_im,mul_zero,zero_mul,add_zero,zero_add]

section Blocks
variable {A B : Type*}

/-- Ordered block addressing for symbolic block width and query count. -/
def blockIndex {m n : Nat} (i : Fin n) (j : Fin m) : Fin (m*n) :=
  ⟨m*i.val+j.val,by
    calc
      m*i.val+j.val < m*(i.val+1) := by
        simpa only [Nat.mul_add,Nat.mul_one] using Nat.add_lt_add_left j.isLt (m*i.val)
      _ ≤ m*n := Nat.mul_le_mul_left m i.isLt⟩

theorem flatten_blocks {m n : Nat} (p : Fin n → A) (g : A → List B)
    (f : Fin (m*n) → B)
    (block : ∀ i, g (p i)=List.ofFn fun j=>f (blockIndex i j)) :
    (List.ofFn p).flatMap g=List.ofFn f := by
  rw [List.flatMap_def,List.map_ofFn]
  simp only [Function.comp_def]
  simp_rw [block]
  exact (List.ofFn_mul' f).symm

theorem ofFn_four (f : Fin 4 → B) : List.ofFn f=[f 0,f 1,f 2,f 3] := rfl
theorem ofFn_two (f : Fin 2 → B) : List.ofFn f=[f 0,f 1] := rfl

theorem block_four {q : Nat} (i : Fin q) (j : Fin 4) :
    blockIndex i j=childIndex i j := rfl
theorem block_two_false {q : Nat} (i : Fin q) :
    blockIndex i (0 : Fin 2)=baseIndex i false := rfl
theorem block_two_true {q : Nat} (i : Fin q) :
    blockIndex i (1 : Fin 2)=baseIndex i true := rfl
end Blocks

/-- (++,+−,−−,−+) is exactly the existing sourceDenom slot convention. -/
theorem point_values (d : Data (K := K)) (i : Fin 262144) :
    LineNormBuffer.pointValues d.a d.b d.c (point i)=
      List.ofFn (sourceDenom d i) := by
  rw [ofFn_four]
  dsimp only [LineNormBuffer.pointValues]
  rw [scale_eq_mul,scale_eq_mul,point_x,point_y]
  simp only [sourceDenom,xs,ys,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,
    mul_neg,sub_eq_add_neg]

theorem values_eq {q : Nat} (d : Data (K := K)) (queries : Fin q → Fin 262144) :
    LineNormBuffer.values d.a d.b d.c (points queries)=denominatorList d queries := by
  unfold LineNormBuffer.values points denominatorList
  apply flatten_blocks (m := 4)
  intro i
  rw [point_values]
  apply congrArg (fun f : Fin 4 → K=>List.ofFn f)
  funext j
  rw [block_four]
  simp only [denomArray,parentIndex_childIndex,slotIndex_childIndex]

theorem base_false {q : Nat} (queries : Fin q → Fin 262144) (i : Fin q) :
    baseArray queries (baseIndex i false)=2*(point (queries i)).val.1 := by
  unfold baseArray
  rw [baseParent_index]
  have even : (baseIndex i false).val%2=0 := by
    simp only [baseIndex,Bool.false_eq_true,ite_false]
    omega
  rw [if_pos even]
  rfl

theorem base_true {q : Nat} (queries : Fin q → Fin 262144) (i : Fin q) :
    baseArray queries (baseIndex i true)=2*(point (queries i)).val.2 := by
  unfold baseArray
  rw [baseParent_index]
  have odd : (baseIndex i true).val%2≠0 := by
    simp only [baseIndex,ite_true]
    omega
  rw [if_neg odd]
  rfl

theorem base_eq {q : Nat} (queries : Fin q → Fin 262144) :
    LineNormBuffer.base (points queries)=baseList queries := by
  unfold LineNormBuffer.base points baseList
  apply flatten_blocks (m := 2)
  intro i
  rw [ofFn_two,block_two_false,block_two_true,base_false,base_true]

theorem lengths {q : Nat} (d : Data (K := K)) (queries : Fin q → Fin 262144) :
    (LineNormBuffer.values d.a d.b d.c (points queries)).length=4*q ∧
    (LineNormBuffer.norms d.a d.b d.c (points queries)).length=4*q ∧
    (LineNormBuffer.base (points queries)).length=2*q ∧
    (LineNormBuffer.lines (points queries)).length=q := by
  simpa only [points,List.length_ofFn] using
    LineNormBuffer.buffer_lengths d.a d.b d.c (points queries)

/-- Complete derived field/list constructor into the checked ordered query API.
No reciprocal, line/norm-buffer, or denominator-list equality is a premise. -/
theorem inverse_eq {q : Nat} (d : Data (K := K)) (queries : Fin q → Fin 262144) :
    LineNormBuffer.inverseLines d.a d.b d.c (points queries)=
      QueriedInverse.checked (denominatorList d queries) (baseList queries) := by
  rw [LineNormBuffer.inverseLines_eq_checked,values_eq,base_eq]

theorem success_residual {q : Nat} (d : Data (K := K))
    (received : Fin 1048576 → K) (queries : Fin q → Fin 262144)
    (out : List K × List M31Exact)
    (success : LineNormBuffer.inverseLines d.a d.b d.c (points queries)=some out)
    (alpha : K) (final : Fin 256 → K) (i : Fin q) :
    exactFinalLinear final (queries i)-QueriedResidual.sourceFold d received queries out alpha i=
      PostQueryFunctional.residual final (fun j=>storedPoint (K := K) (queries j))
        ((SelectedReceivedOracle.oracle (0 : Fin 1024 → K)
          (SelectedQuotientOriginal.virtual d received)).folded alpha) i := by
  have checked := (inverse_eq d queries).symm.trans success
  exact QueriedResidual.success_residual d received queries out checked alpha final i

theorem queried_pole_reject {q : Nat} (d : Data (K := K))
    (queries : Fin q → Fin 262144) (i : Fin q) (j : Fin 4)
    (pole : SelectedQuotientOriginal.denominator d (childIndex (queries i) j)=0) :
    LineNormBuffer.inverseLines d.a d.b d.c (points queries)=none := by
  rw [inverse_eq]
  exact QueriedResidual.queried_pole_reject d queries (baseList queries) i j pole

#print axioms point_nonzero
#print axioms scale_eq_mul
#print axioms flatten_blocks
#print axioms point_values
#print axioms values_eq
#print axioms base_eq
#print axioms lengths
#print axioms inverse_eq
#print axioms success_residual
#print axioms queried_pole_reject
end
end AspisV8.SelectedQueryBuffer
