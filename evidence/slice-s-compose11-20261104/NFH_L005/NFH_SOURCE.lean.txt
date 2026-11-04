import NFH_ComparisonBoundary
import NFD_ScanConditional
set_option autoImplicit false
namespace NFH_ComparisonDomain
open Aeneas Aeneas.Std
open NFH_ComparisonBoundary

/-- Only the reached688-byte domain is proposed for runtime certification. -/
def At688Law (reply : List U8 → List U8 → Int) : Prop :=
  ∀ left right, left.length = 688 → right.length = 688 →
    ZeroLaw left right (reply left right)

/-- Mathematical completion outside the native call domain. It has no native
credit: the caller must separately establish both actual buffer lengths. -/
def complete688 (reply : List U8 → List U8 → Int) (left right : List U8) : Bool :=
  if left.length = 688 ∧ right.length = 688 then decide (reply left right = 0)
  else NEU_EqualityLoop.equalBytes left right

theorem complete688_on_domain (reply : List U8 → List U8 → Int)
    (left right : List U8) (leftSize : left.length = 688)
    (rightSize : right.length = 688) :
    complete688 reply left right = decide (reply left right = 0) := by
  simp only [complete688,leftSize,rightSize,and_self,if_true]

/-- Conditional interface conversion, not discharge of At688Law and not a
scanner theorem. No runtime fact about other lengths is assumed. -/
theorem complete688_association (reply : List U8 → List U8 → Int)
    (runtime688Law : At688Law reply) :
    NFD_ScanConditional.NativeEqualityAssociation (complete688 reply) := by
  intro left right
  have loop : NEU_EqualityLoop.equalBytes left right = decide (left = right) :=
    congrArg Prod.fst (NEU_EqualityLoop.prefix_frame left right ())
  unfold complete688
  split
  next sizes =>
    rw [reply_eq_loop left right (reply left right)
      (runtime688Law left right sizes.1 sizes.2)]
    exact loop
  next => exact loop

#print axioms complete688_on_domain
#print axioms complete688_association
end NFH_ComparisonDomain
