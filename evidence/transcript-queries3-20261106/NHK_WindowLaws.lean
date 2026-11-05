import NHB_Membership
set_option autoImplicit false
namespace AspisR1.NHK_WindowLaws
open Aeneas Aeneas.Std

theorem append (x : U32) (left right : List U32) :
    NHB_Membership.reference x (left ++ right) =
      (NHB_Membership.reference x left || NHB_Membership.reference x right) := by
  simp only [NHB_Membership.reference_eq,List.mem_append]
  by_cases hl : x ∈ left <;> by_cases hr : x ∈ right <;> simp [hl,hr]

theorem prefix_split (x : U32) (xs : List U32) (length cut : Nat)
    (bound : cut ≤ length) :
    NHB_Membership.reference x (xs.take length) =
      (NHB_Membership.reference x (xs.take cut) ||
       NHB_Membership.reference x ((xs.drop cut).take (length-cut))) := by
  have shape : xs.take length = xs.take cut ++ (xs.drop cut).take (length-cut) := by
    have size : cut+(length-cut)=length := by omega
    simpa only [size] using (show xs.take (cut+(length-cut)) = xs.take cut ++ (xs.drop cut).take (length-cut) from List.take_add)
  rw [shape,append]

/-- A failed whole-length native check is never replaced by a shorter prefix.
Both replies, on the same disjoint windows, are required by this adapter. -/
theorem native_split (x : U32) (xs : List U32) (length cut : Nat)
    (bound : cut ≤ length) (native left right : Bool)
    (nativeEdge : native = (left || right))
    (leftEdge : left = NHB_Membership.reference x (xs.take cut))
    (rightEdge : right = NHB_Membership.reference x ((xs.drop cut).take (length-cut))) :
    native = NHB_Membership.reference x (xs.take length) := by
  rw [nativeEdge,leftEdge,rightEdge,← prefix_split x xs length cut bound]

#print axioms append
#print axioms prefix_split
#print axioms native_split
end AspisR1.NHK_WindowLaws
