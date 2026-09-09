import ExactFoldSelected
import CausalOrderedRelation

/-! The SAME arbitrary selected indexed quotient word supplies the relation
game's field-domain oracle. The corruption set is the entire domain, so no
polynomiality or anchor-support premise is hidden in this constructor.
This is mathematical index/field transport, not authenticated Rust replay. -/
set_option autoImplicit false
set_option maxRecDepth 200
set_option maxHeartbeats 300000
namespace AspisV8.SelectedReceivedOracle
open Finset
open AspisV5ComponentCQM31TowerExact
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriConcreteEncoderCommutation
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisK1.V7Tag73CanonicalOneFoldSchedule
open AspisV8.PostQueryFunctional AspisV8.CausalOrderedRelation

noncomputable section
abbrev K := QM31Exact

local instance twoNonzero : NeZero (2 : K) := ⟨by
  intro h
  have equation := (canonical_one_fold_schedule_exact 0).1 ⟨0, by decide⟩
  have impossible : (0 : K)=1 := by simpa only [h,zero_mul] using equation
  exact zero_ne_one impossible⟩

def domain : Finset K := Finset.univ.image (storedPoint (K := K))

theorem domain_card : domain.card=262144 := by
  rw [domain,Finset.card_image_of_injective _ storedPoint_injective]
  simp only [Finset.card_univ,Fintype.card_fin]

def index (t : K) : Fin 262144 :=
  if h : ∃ i : Fin 262144, storedPoint (K := K) i=t then Classical.choose h else 0

theorem index_point (i : Fin 262144) : index (storedPoint (K := K) i)=i := by
  unfold index
  split
  · rename_i h
    exact storedPoint_injective (Classical.choose_spec h)
  · rename_i h
    exact False.elim (h ⟨i,rfl⟩)

theorem point_index (t : K) (ht : t∈domain) : storedPoint (K := K) (index t)=t := by
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ht
  rw [index_point]

theorem x_nonzero (i : Fin 262144) : exactCircleX i≠0 := by
  intro h
  have equation := (canonical_one_fold_schedule_exact 0).1 i
  have impossible : (0 : K)=1 := by simpa only [h,mul_zero,zero_mul] using equation
  exact zero_ne_one impossible

theorem y_nonzero (i : Fin 262144) : exactCircleY i≠0 := by
  intro h
  have equation := (canonical_one_fold_schedule_exact 0).2 i
  have impossible : (0 : K)=1 := by simpa only [h,mul_zero,zero_mul] using equation
  exact zero_ne_one impossible

theorem inverse_unique (a b : K) (h : a*b=1) : b=a⁻¹ := by
  have hn : a≠0 := by
    intro hz
    exact zero_ne_one (by simpa only [hz,zero_mul] using h)
  apply mul_left_cancel₀ hn
  exact h.trans (mul_inv_cancel₀ hn).symm

theorem inverse_x (i : Fin 262144) :
    algebraMap M31Exact K ((canonicalOneFoldSchedule 0).circleInv2x i)=
      (2*exactCircleX i)⁻¹ :=
  inverse_unique _ _ ((canonical_one_fold_schedule_exact 0).1 i)

theorem inverse_y (i : Fin 262144) :
    algebraMap M31Exact K ((canonicalOneFoldSchedule 0).circleInv2y i)=
      (2*exactCircleY i)⁻¹ :=
  inverse_unique _ _ ((canonical_one_fold_schedule_exact 0).2 i)

/-- Arbitrary received slots, with the actual exact stored domain. Q is an
analysis parameter; no assumption connects it to the received values. -/
def oracle (Q : Fin 1024 → K) (received : Fin 1048576 → K) :
    FixedOracle domain domain Q where
  x := fun t=>exactCircleX (index t)
  y := fun t=>exactCircleY (index t)
  slots := fun t slot=>received (childIndex (index t) slot)
  x_nonzero := fun t _=>x_nonzero (index t)
  y_nonzero := fun t _=>y_nonzero (index t)
  coordinate := by
    intro t ht
    exact (storedPoint_source_pi (K := K) (index t)).symm.trans (point_index t ht)
  supported := fun t ht notIn=>False.elim (notIn ht)

theorem oracle_slots (Q : Fin 1024 → K) (received : Fin 1048576 → K)
    (i : Fin 262144) (slot : Fin 4) :
    (oracle Q received).slots (storedPoint (K := K) i) slot=received (childIndex i slot) := by
  simp only [oracle,index_point]

/-- The game receives exactly the normalized fold used by the selected
geometric recovery theorem, not a second free word supplied through a bridge. -/
theorem oracle_folded (Q : Fin 1024 → K) (received : Fin 1048576 → K)
    (alpha : K) (i : Fin 262144) :
    (oracle Q received).folded alpha (storedPoint (K := K) i)=
      circleFoldLayer 262144 alpha (canonicalOneFoldSchedule 0).circleInv2x
        (canonicalOneFoldSchedule 0).circleInv2y received i := by
  rw [circleFoldLayer_apply]
  simp only [FixedOracle.folded,oracle,index_point]
  rw [inverse_x,inverse_y]

theorem final_evaluation (final : Fin 256 → K) (i : Fin 262144) :
    lineEval final (storedPoint (K := K) i)=exactFinalLinear final i := rfl

/-- Pointwise residuals, including their sign and original query order, are
those of the SAME selected indexed final and received quotient. -/
theorem query_residual {q : Nat} (Q : Fin 1024 → K) (received : Fin 1048576 → K)
    (final : Fin 256 → K) (alpha : K) (queries : Fin q → Fin 262144) (j : Fin q) :
    PostQueryFunctional.residual final (fun t=>storedPoint (K := K) (queries t))
      ((oracle Q received).folded alpha) j =
    exactFinalLinear final (queries j)-circleFoldLayer 262144 alpha
      (canonicalOneFoldSchedule 0).circleInv2x
      (canonicalOneFoldSchedule 0).circleInv2y received (queries j) := by
  simp only [PostQueryFunctional.residual,final_evaluation,oracle_folded]

#print axioms domain_card
#print axioms index_point
#print axioms point_index
#print axioms inverse_x
#print axioms inverse_y
#print axioms oracle
#print axioms oracle_slots
#print axioms oracle_folded
#print axioms final_evaluation
#print axioms query_residual
end
end AspisV8.SelectedReceivedOracle
