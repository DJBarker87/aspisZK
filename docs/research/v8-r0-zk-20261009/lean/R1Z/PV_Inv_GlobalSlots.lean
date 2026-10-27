import R1Z.PV_Inv_RawRun
set_option autoImplicit false
namespace R1Z.PV_Inv_GlobalSlots
open PV_Inv_RawSlots
variable {I V W : Type} [DecidableEq I] [Zero W] [DecidableEq W]
abbrev State (I V W : Type) := I → Slots V W

def step (s : State I V W) (e : I × Entry V W) : Option (State I V W) :=
  (PV_Inv_RawSlots.step (s e.1) e.2).map (fun localState => Function.update s e.1 localState)

def run (s : State I V W) : List (I × Entry V W) → Option (State I V W)
 | [] => some s
 | e::es => (step s e).bind (fun t => run t es)

def Good (P : I → V → Prop) (s : State I V W) := ∀ i, PV_Inv_RawSlots.Good (P i) (s i)

theorem step_good (P : I → V → Prop) (s t : State I V W) (e : I × Entry V W)
    (hs : Good P s) (he : P e.1 e.2.value) (hr : step s e=some t) : Good P t := by
  unfold step at hr
  cases hl : PV_Inv_RawSlots.step (s e.1) e.2 with
  | none => simp [hl] at hr
  | some u =>
    simp only [hl,Option.map_some,Option.some.injEq] at hr
    subst t
    intro i
    by_cases hi : i=e.1
    · subst i
      simpa only [Function.update_self] using PV_Inv_RawSlots.step_good (P e.1) (s e.1) u e.2 (hs e.1) he hl
    · simpa [hi] using hs i

#print axioms step_good
end R1Z.PV_Inv_GlobalSlots
