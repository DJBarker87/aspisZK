import R1Z.PV_ROWS10B_Consumed
set_option autoImplicit false
namespace R1Z.PV_ROWS10B_Satisfiable
open Aeneas Aeneas.Std PV_ROWS10B_Consumed
/-- Explicit model instance, not a claimed deployed execution. The two
witnesses share the same public environment. All four Result branches occur
at different lengths, so non-vacuity is not obtained by deleting errors. -/
def backend (_ : Bool) (s : Slice U8) :
    Result ((core.result.Result Unit Unit) × Slice U8) :=
  if s.val.length = 1 then .ok (.Err (), s) else
  if s.val.length = 2 then .fail .panic else
  if s.val.length = 3 then .div else .ok (.Ok (), s)
def source (w : Bool) : Op Unit := fill (backend w)
def word (_ : Bool) (_ : Unit) : Unit := ()
def interpret (_ : Unit) (n : Nat) : Stop :=
  if n = 1 then .returned true else
  if n = 2 then .aborted .panic else
  if n = 3 then .diverged else .returned false
/-- This literal model density instantiates the same E1 schema; it says
nothing about Linux entropy quality. -/
def law (_ : Unit) (_ : Bool) : ℚ := 1 / (Fintype.card Bool : ℚ)

theorem all_links :
    PV_ROWS10B_Link_Entry source source ∧
    PV_ROWS10B_Link_Body source backend ∧
    PV_ROWS10B_Link_Control backend word interpret ∧
    PV_ROWS10B_Link_Public word ∧
    PV_ROWS10B_Link_Callback law law ∧
    (∀ c raw, law c raw = 1 / (Fintype.card Bool : ℚ)) := by
  refine ⟨rfl, ?_, ?_, ?_, rfl, ?_⟩
  · intro w s; rfl
  · intro w c s
    simp only [backend, word, interpret]
    split <;> simp_all only [stop]
    split <;> simp_all only [stop]
    split <;> rfl
  · intro a b c; rfl
  · intro c raw; rfl

/-- Existential witness for the conjunction, using the exact op129 carrier. -/
theorem satisfiable : ∃ (native source' backend' : Bool → Op Unit)
    (word' : Bool → Unit → Unit) (interpret' : Unit → Nat → Stop)
    (callback law' : Unit → Bool → ℚ),
    PV_ROWS10B_Link_Entry native source' ∧
    PV_ROWS10B_Link_Body source' backend' ∧
    PV_ROWS10B_Link_Control backend' word' interpret' ∧
    PV_ROWS10B_Link_Public word' ∧
    PV_ROWS10B_Link_Callback callback law' ∧
    (∀ c raw, law' c raw = 1 / (Fintype.card Bool : ℚ)) :=
  ⟨source, source, backend, word, interpret, law, law, all_links⟩
#print axioms all_links
#print axioms satisfiable
end R1Z.PV_ROWS10B_Satisfiable
