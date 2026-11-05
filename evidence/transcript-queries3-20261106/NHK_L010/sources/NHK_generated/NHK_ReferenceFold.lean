import NHK_WindowLaws
set_option autoImplicit false
namespace AspisR1.NHK_ReferenceFold
open Aeneas Aeneas.Std

/-- Flat, effect-free scalar comparisons in the two native reference windows.
No canonicality or successful-sampler restriction is required. -/
theorem scalar_fold (x : U32) (xs : List U32) (seed : Bool) :
    xs.foldl (fun acc y => acc || decide (y=x)) seed =
      (seed || NHB_Membership.reference x xs) := by
  induction xs generalizing seed with
  | nil => cases seed <;> rfl
  | cons y ys ih =>
    simp only [List.foldl_cons,ih]
    by_cases h : y=x <;> simp [NHB_Membership.reference,h]

theorem split_windows (x : U32) (xs : List U32) (length cut : Nat)
    (bound : cut ≤ length) :
    ((xs.take cut).foldl (fun acc y => acc || decide (y=x)) false ||
      ((xs.drop cut).take (length-cut)).foldl (fun acc y => acc || decide (y=x)) false) =
      NHB_Membership.reference x (xs.take length) := by
  rw [scalar_fold,scalar_fold]
  simpa only [Bool.false_or] using (NHK_WindowLaws.prefix_split x xs length cut bound).symm

#print axioms scalar_fold
#print axioms split_windows
end AspisR1.NHK_ReferenceFold
