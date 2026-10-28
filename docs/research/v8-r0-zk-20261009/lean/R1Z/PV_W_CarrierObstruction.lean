import R1Z.PV_W_Threading
set_option autoImplicit false
namespace R1Z.PV_W_CarrierObstruction
open PV_W_Threading
variable {W C E A : Type}

/-- A world interpretation must factor native outcomes through its chosen
world projection. The premise here is projection equality, not an assumption
of native outcome equality. -/
theorem no_factor {N : Type} (project : N → W) (native : N → Outcome E A)
    (left right : N) (same : project left = project right)
    (different : native left ≠ native right) :
    ¬ ∃ interpret : W → Outcome E A, ∀ n, interpret (project n) = native n := by
  intro ⟨interpret,law⟩
  exact different ((law left).symm.trans ((congrArg interpret same).trans (law right)))

/-- Threading additional copies of an insufficient World does not repair the
projection: the complete interpreter's outcome still factors through World. -/
theorem no_state_interpreter {N : Type} (project : N → W) (native : N → Outcome E A)
    (left right : N) (same : project left = project right)
    (different : native left ≠ native right) :
    ¬ ∃ interpret : M W C E A, ∀ n, (interpret (project n)).outcome = native n := by
  intro ⟨interpret,law⟩
  exact no_factor project native left right same different ⟨fun w => (interpret w).outcome,law⟩

/-- Counterexample family reusing FXM's independently checked normal/panic
native witness. Bool is external destructor-accessible state, not the input's
value and not one of the existing OS tape/cursor fields. -/
def destructor (n : W × Bool) : Outcome Unit Unit :=
  if n.2 then .fail () else .ok ()

theorem distinct (w : W) : destructor (w,false) ≠ destructor (w,true) := by
  intro h
  cases h

theorem no_forgotten_flag_interpreter (w : W) :
    ¬ ∃ interpret : M W C Unit Unit,
      ∀ n : W × Bool, (interpret n.1).outcome = destructor n :=
  no_state_interpreter Prod.fst destructor (w,false) (w,true) rfl (distinct w)

/-- Enriching the interpreter's P state repairs this particular information
loss; it is not evidence of native allocator or generic Drop adequacy. -/
def retainedFlag : M (W × Bool) C Unit Unit := fun n => ⟨destructor n,n,[]⟩

theorem retainedFlag_result (n : W × Bool) :
    (retainedFlag (C := C) n).outcome = destructor n := rfl

#print axioms no_factor
#print axioms no_state_interpreter
#print axioms distinct
#print axioms no_forgotten_flag_interpreter
#print axioms retainedFlag_result
end R1Z.PV_W_CarrierObstruction
