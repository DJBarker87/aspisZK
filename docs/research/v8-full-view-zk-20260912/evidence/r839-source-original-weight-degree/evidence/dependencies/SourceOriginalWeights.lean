import AspisV8R17.TransportedOpening
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Source-shaped original_weights materialization. Points are the three
caller-supplied length-10 arrays; the source point-construction refinement and
the structured-mask weight/evaluation identity are separate obligations. -/
set_option autoImplicit false
namespace AspisV8R17
open scoped BigOperators
variable {F : Type*} [CommRing F]

def sourceMultilinearFactors (point : Fin 10 → F) (index : ℕ) : List F :=
  List.ofFn fun coordinate : Fin 10 =>
    if (index >>> (9-coordinate.val)) &&& 1 = 0 then 1-point coordinate else point coordinate

def sourceMultilinearWeight (scale : F) (point : Fin 10 → F) (index : ℕ) : F :=
  (sourceMultilinearFactors point index).foldl (fun value factor => value*factor) scale

def sourcePointBasis (point : Fin 10 → F) (index : ℕ) : F :=
  (sourceMultilinearFactors point index).prod

theorem source_product_loop (xs : List F) (scale : F) :
    xs.foldl (fun value factor => value*factor) scale = scale*xs.prod := by
  induction xs generalizing scale with
  | nil => simp
  | cons x xs ih => simp [ih, mul_assoc]

theorem sourceMultilinearWeight_eq (scale : F) (point : Fin 10 → F) (index : ℕ) :
    sourceMultilinearWeight scale point index = scale*sourcePointBasis point index :=
  source_product_loop _ _

def sourceOriginalWeight (points : Fin 3 → Fin 10 → F) (kappa : F)
    (inactive : Finset (Fin 1024)) (g : Fin 1024 → F) (structured : Bool)
    (i : Fin 1024) : F :=
  let components := if structured then
    [(kappa^2,points 1),(kappa^2*kappa,points 2)] else
    [(kappa,points 0),(kappa^2,points 1),(kappa^2*kappa,points 2)]
  let total := components.foldl
    (fun acc component => acc+sourceMultilinearWeight component.1 component.2 i.val) 0
  let withInactive := if i ∈ inactive then total+1 else total
  if structured then withInactive+kappa*g i else withInactive

theorem sourceOriginalWeight_eq (points : Fin 3 → Fin 10 → F) (kappa : F)
    (inactive : Finset (Fin 1024)) (g : Fin 1024 → F) (structured : Bool)
    (i : Fin 1024) :
    sourceOriginalWeight points kappa inactive g structured i =
      kappa*(if structured then g i else sourcePointBasis (points 0) i.val) +
      kappa^2*sourcePointBasis (points 1) i.val +
      kappa^3*sourcePointBasis (points 2) i.val + (if i ∈ inactive then 1 else 0) := by
  cases structured <;> by_cases hi : i ∈ inactive <;>
    simp [sourceOriginalWeight, sourceMultilinearWeight_eq, hi] <;> ring

def sourcePointFunctional (point : Fin 10 → F) (m : Fin 1024 → F) : F :=
  ∑ i, sourcePointBasis point i.val*m i

theorem sourceOriginalWeight_dot (points : Fin 3 → Fin 10 → F) (kappa : F)
    (inactive : Finset (Fin 1024)) (g m : Fin 1024 → F) (structured : Bool) :
    (∑ i, sourceOriginalWeight points kappa inactive g structured i*m i) =
      kappa*(if structured then ∑ i, g i*m i else sourcePointFunctional (points 0) m) +
      kappa^2*sourcePointFunctional (points 1) m +
      kappa^3*sourcePointFunctional (points 2) m + ∑ i ∈ inactive, m i := by
  simp only [sourceOriginalWeight_eq, sourcePointFunctional, add_mul,
    Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, ite_mul, one_mul, zero_mul]
  have hsum : (∑ i : Fin 1024, if i ∈ inactive then m i else 0) = ∑ i ∈ inactive, m i := by
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext i; simp
    · intro i hi; rfl
  rw [hsum]
  cases structured <;> rfl

theorem original_weights_transported_pairing (half : F)
    (points : Fin 3 → Fin 10 → F) (kappa : F)
    (inactive : Finset (Fin 1024)) (pivot : Fin 1024) (order : Fin 1024 ≃ Fin 1024)
    (g : Fin 1024 → F) (q : ℕ → F) (a b c tau : F) (structured : Bool) :
    let m := AspisV8R16.inverseTransport inactive pivot order
      (fun j => sourceChord half q a b c j.val)
    rangeDot 1024 (sourceQuotientWeights half
      (extendFin1024 (AspisV8R16.transportDual inactive pivot order
        (sourceOriginalWeight points kappa inactive g structured))) a b c tau structured) q =
      (kappa*(if structured then ∑ i, g i*m i else sourcePointFunctional (points 0) m) +
        kappa^2*sourcePointFunctional (points 1) m +
        kappa^3*sourcePointFunctional (points 2) m + ∑ i ∈ inactive, m i) +
      (if structured then tau^3 else tau)*q 1023 +
      (if structured then tau^4 else tau^2)*(b*q 1022-c*q 1021) := by
  dsimp only
  rw [transported_source_opening_pairing, sourceOriginalWeight_dot]

#print axioms source_product_loop
#print axioms sourceMultilinearWeight_eq
#print axioms sourceOriginalWeight_eq
#print axioms sourceOriginalWeight_dot
#print axioms original_weights_transported_pairing
end AspisV8R17
