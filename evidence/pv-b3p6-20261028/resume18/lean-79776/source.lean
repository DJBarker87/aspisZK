import PV_B3P_PreconditionFormatting569227
namespace PV_B3P_IndexRangeFormatting569227
open Aeneas Aeneas.Std core.ops.range PV_B3P_PreconditionFormatting569227
set_option autoImplicit false
/-- Internal iterator invariant. Its construction at native IntoIter callers is
separate; no endpoint assumption is added by this local control model. -/
abbrev Cursor (length : Usize) :=
  {r : Range Usize // r.start.val ≤ r.end.val ∧ r.end.val ≤ length.val}

def advance {length : Usize} (c : Cursor length) (active : c.val.start ≠ c.val.end) :
    Cursor length :=
  ⟨{c.val with start := Usize.wrapping_add c.val.start 1#usize},
    (index_range_conditions _ _ c.property.1 active).2.2,c.property.2⟩

theorem shared_index_bound {length : Usize} (c : Cursor length)
    (active : c.val.start ≠ c.val.end) : c.val.start.val < length.val := by
  have inside := (index_range_conditions _ _ c.property.1 active).1
  have bound := c.property.2
  omega

/-- IndexRange try_fold's unchecked increment precedes the callback, including
its residual branch. The callback retains arbitrary Result behaviour. -/
def body {α β : Type} {length : Usize} (add_panic : Result Unit)
    (step : α → Usize → Result (ControlFlow α β)) (s : Cursor length × α) :
    Result (ControlFlow (Cursor length × α) (Cursor length × ControlFlow α β)) :=
  if active : s.1.val.start ≠ s.1.val.end then do
    let _ ← check add_panic (s.1.val.start.val+1 ≤ UScalar.max .Usize)
    let next := advance s.1 active
    let answer ← step s.2 s.1.val.start
    match answer with
    | .cont accum => .ok (.cont (next,accum))
    | .done residual => .ok (.done (next,.done residual))
  else .ok (.done (s.1,.cont s.2))

theorem body_independent {α β : Type} {length : Usize} (first second : Result Unit)
    (step : α → Usize → Result (ControlFlow α β)) (s : Cursor length × α) :
    body first step s = body second step s := by
  by_cases active : s.1.val.start ≠ s.1.val.end
  · have safe := (index_range_conditions _ _ s.1.property.1 active).2.1
    simp only [body,dif_pos active,check_safe _ _ safe]
  · simp only [body,dif_neg active]

def source {α β : Type} {length : Usize} (assert_panic add_panic : Result Unit)
    (step : α → Usize → Result (ControlFlow α β)) (s : Cursor length × α) := do
  let _ ← check assert_panic (s.1.val.start.val ≤ s.1.val.end.val)
  loop (body add_panic step) s

theorem handler_independent {α β : Type} {length : Usize}
    (assert1 add1 assert2 add2 : Result Unit)
    (step : α → Usize → Result (ControlFlow α β)) (s : Cursor length × α) :
    source assert1 add1 step s = source assert2 add2 step s := by
  unfold source
  simp only [check_safe _ _ s.1.property.1,bind_tc_ok]
  rw [funext (body_independent add1 add2 step)]

/-- Shared get_unchecked in the captured array-fold closure has the exact
emitted cursor, rather than an unrelated mathematical loop counter. -/
theorem shared_check {length : Usize} (panic : Result Unit) (c : Cursor length)
    (active : c.val.start ≠ c.val.end) :
    check panic (c.val.start.val < length.val) = .ok () :=
  check_safe _ _ (shared_index_bound c active)
#print axioms shared_index_bound
#print axioms body_independent
#print axioms handler_independent
#print axioms shared_check
end PV_B3P_IndexRangeFormatting569227
