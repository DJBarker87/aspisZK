import R1Z.PV_Inv_Pack
set_option autoImplicit false
namespace R1Z.PV_Inv_PackList
open PV_Inv_Pack
variable {K : Type} [Field K] [DecidableEq K]

def run (s : Slots K) : List (Endpoint K) → Option (Slots K)
  | [] => some s
  | e::es => (step s e).bind (fun t => run t es)

theorem preserves (chi : K) (es : List (Endpoint K)) (s t : Slots K)
    (hs : Safe chi s) (hp : ∀ e ∈ es, chi ≠ e.value)
    (hr : run s es = some t) : Safe chi t := by
  induction es generalizing s with
  | nil => cases hr; exact hs
  | cons e es ih =>
    simp only [run] at hr
    cases he : step s e with
    | none => simp [he] at hr
    | some u =>
      simp only [he,Option.bind_some] at hr
      apply ih u (step_safe chi s u e hs (hp e (by simp)) he)
      · intro e' h
        exact hp e' (by simp [h])
      · exact hr

theorem from_empty (chi : K) (es : List (Endpoint K)) (t : Slots K)
    (hp : ∀ e ∈ es, chi ≠ e.value) (hr : run empty es = some t) : Safe chi t :=
  preserves chi es empty t (empty_safe chi) hp hr

#print axioms preserves
#print axioms from_empty
end R1Z.PV_Inv_PackList
