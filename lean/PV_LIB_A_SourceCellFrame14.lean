import PV_LIB_A_CallFrame13
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_SourceCellFrame14
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine

/-- SOURCE cells below a live activation boundary; no activation-counter equality
is part of this frame interface. -/
def Below (limit : Nat) (s t : Store Data) : Prop :=
  ∀ p, p.activation < limit → t.cells p = s.cells p

theorem refl (limit : Nat) (s : Store Data) : Below limit s s := by intro p hp; rfl
theorem trans (limit : Nat) (s t u : Store Data) (h : Below limit s t) (g : Below limit t u) : Below limit s u := by
  intro p hp; rw [g p hp,h p hp]

def Local : PV_STX2_Syntax.Place → Prop
  | .local _ => True
  | .project p (.field _) => Local p
  | _ => False

theorem located (C : Carrier OWNER Data) (s : Store Data) (w : OWNER) (a : Nat)
    (p : PV_STX2_Syntax.Place) (q : Address) (own : Local p) (found : locate C s w a p = some q) :
    q.activation = a := by
  induction p generalizing q with
  | «local» n => cases found; rfl
  | «global» n => cases own
  | project p projection ih =>
    cases projection with
    | deref => cases own
    | metadata => cases own
    | field n =>
      cases h : locate C s w a p with
      | none => simp [locate,h] at found
      | some r =>
        simp only [locate,h,Option.bind_some] at found
        cases found
        exact ih r own h

theorem write_frame (limit : Nat) (s : Store Data) (q : Address) (v : Option Data)
    (later : limit ≤ q.activation) : Below limit s (write s q v) := by
  intro p hp
  apply write_other
  intro eq
  have bad := congrArg Address.activation eq
  omega

/-- A projected write changes only its root's activation, for every replacement
and every defined field rebuild, including arbitrary aggregate payloads. -/
theorem writeAddress_frame (C : Carrier OWNER Data) (limit : Nat) (s t : Store Data)
    (q : Address) (v : Option Data) (later : limit ≤ q.activation)
    (written : writeAddress C s q v = some t) : Below limit s t := by
  cases fields : q.fields with
  | nil =>
    simp only [writeAddress,fields] at written
    cases written
    exact write_frame limit s q v later
  | cons n ns =>
    cases root : s.cells {q with fields := []} with
    | none => simp [writeAddress,fields,root] at written
    | some old =>
      cases changed : replaceFields C (n::ns) v old with
      | none => simp [writeAddress,fields,root,changed] at written
      | some new =>
        simp [writeAddress,fields,root,changed] at written
        cases written
        exact write_frame limit s {q with fields := []} (some new) later

#print axioms Below
#print axioms refl
#print axioms trans
#print axioms located
#print axioms write_frame
#print axioms writeAddress_frame
end PV_LIB_A_SourceCellFrame14
