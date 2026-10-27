import R1Z.PV_Inv_RawSlots
set_option autoImplicit false
namespace R1Z.PV_Inv_RawRun
open PV_Inv_RawSlots
variable {V W : Type} [Zero W] [DecidableEq W]

def run (s : Slots V W) : List (Entry V W) → Option (Slots V W)
  | [] => some s
  | e::es => (step s e).bind (fun t => run t es)

theorem preserves (P : V → Prop) (es : List (Entry V W)) (s t : Slots V W)
    (hs : Good P s) (hp : ∀ e ∈ es, P e.value) (hr : run s es = some t) : Good P t := by
  induction es generalizing s with
  | nil => cases hr; exact hs
  | cons e es ih =>
    simp only [run] at hr
    cases he : step s e with
    | none => simp [he] at hr
    | some u =>
      simp only [he,Option.bind_some] at hr
      apply ih u (step_good P s u e hs (hp e (by simp)) he)
      · intro e' h
        exact hp e' (by simp [h])
      · exact hr

def empty (z : V) : Slots V W := fun _ => ⟨z,0⟩

theorem empty_good (P : V → Prop) (z : V) : Good P (empty z : Slots V W) := by
  intro i h
  exact (h rfl).elim

#print axioms preserves
#print axioms empty_good
end R1Z.PV_Inv_RawRun
