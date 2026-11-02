import PV_B3P_PreconditionFormatting569227
namespace PV_B3P_InitializerFormatting569227
open Aeneas Aeneas.Std PV_B3P_PreconditionFormatting569227
set_option autoImplicit false
/-- Numeric control of try_from_fn_erased/push_unchecked. The generator and
write/restoration continuation remain arbitrary Result computations. This does
not associate the native buffer region, Guard destructor or mem::forget. -/
def body {α β σ : Type} (index_panic add_panic : Result Unit) (length : Usize)
    (generate : Usize → Result (ControlFlow α β))
    (store : Usize → α → σ → Result σ) (s : Usize × σ) :
    Result (ControlFlow (Usize × σ) (Usize × ControlFlow σ β)) :=
  if s.1.val < length.val then do
    let item ← generate s.1
    match item with
    | .done residual => .ok (.done (s.1,.done residual))
    | .cont value => do
      let _ ← check index_panic (s.1.val < length.val)
      let written ← store s.1 value s.2
      let _ ← check add_panic (s.1.val+1 ≤ UScalar.max .Usize)
      .ok (.cont (Usize.wrapping_add s.1 1#usize,written))
  else .ok (.done (s.1,.cont s.2))

theorem body_independent {α β σ : Type} (index1 add1 index2 add2 : Result Unit)
    (length : Usize) (generate : Usize → Result (ControlFlow α β))
    (store : Usize → α → σ → Result σ) (s : Usize × σ) :
    body index1 add1 length generate store s =
      body index2 add2 length generate store s := by
  by_cases active : s.1.val < length.val
  · have safe := initializer_conditions s.1 length active
    simp only [body,active,if_true,check_safe _ _ active,check_safe _ _ safe.2.1]
  · simp only [body,active,if_false]

theorem loop_independent {α β σ : Type} (index1 add1 index2 add2 : Result Unit)
    (length : Usize) (generate : Usize → Result (ControlFlow α β))
    (store : Usize → α → σ → Result σ) (s : Usize × σ) :
    loop (body index1 add1 length generate store) s =
      loop (body index2 add2 length generate store) s := by
  rw [funext (body_independent index1 add1 index2 add2 length generate store)]

/-- Starting at zero is independent without assuming any callback succeeds. -/
theorem initial_independent {α β σ : Type} (index1 add1 index2 add2 : Result Unit)
    (length : Usize) (generate : Usize → Result (ControlFlow α β))
    (store : Usize → α → σ → Result σ) (buffer : σ) :
    loop (body index1 add1 length generate store) (0#usize,buffer) =
      loop (body index2 add2 length generate store) (0#usize,buffer) :=
  loop_independent index1 add1 index2 add2 length generate store _
#print axioms body_independent
#print axioms loop_independent
#print axioms initial_independent
end PV_B3P_InitializerFormatting569227
