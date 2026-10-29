import R1Z.PV_ROWS10B_Consumed
set_option autoImplicit false
namespace R1Z.PV_ROWS10B_Dispatch
/-- GETRANDOM_FN's null, usize::MAX sentinel, and callable-pointer states.
The function identity is deliberately not identified with a syscall. -/
inductive Cache (Fn : Type) where
  | cold
  | unavailable
  | callable (fn : Fn)
  deriving DecidableEq
structure Probe where
  returned : Int
  errno : Int
/-- Deployed Linux/glibc cfg, with getrandom_test_linux_fallback unset.
A negative probe falls back ONLY for ENOSYS=38 or EPERM=1. Other errors
retain the resolved function pointer exactly. -/
def initChoice {Fn : Type} (resolved : Option Fn) (probe : Fn → Probe) : Cache Fn :=
  match resolved with
  | none => .unavailable
  | some f =>
    if (probe f).returned < 0 ∧ ((probe f).errno = 38 ∨ (probe f).errno = 1)
      then .unavailable else .callable f

def dispatch {Fn : Type} (cached : Cache Fn) (resolved : Option Fn)
    (probe : Fn → Probe) : Cache Fn :=
  match cached with
  | .cold => initChoice resolved probe
  | .unavailable => .unavailable
  | .callable f => .callable f
/-- The intended syscall wrapper's identity must be an actual loader/cache
invariant. Neither dlsym nor a successful zero-byte probe establishes it. -/
def PV_ROWS10B_Link_SymbolOrigin {Fn : Type} (expected : Fn)
    (cached : Cache Fn) (resolved : Option Fn) : Prop :=
  (∀ f, cached = .callable f → f = expected) ∧
  (∀ f, resolved = some f → f = expected)

theorem selected_origin {Fn : Type} (expected : Fn) (cached : Cache Fn)
    (resolved : Option Fn) (probe : Fn → Probe)
    (origin : PV_ROWS10B_Link_SymbolOrigin expected cached resolved) :
    ∀ f, dispatch cached resolved probe = .callable f → f = expected := by
  intro f hf
  cases cached with
  | unavailable => cases hf
  | callable g => exact origin.1 f (by simpa only [dispatch] using hf)
  | cold =>
    cases resolved with
    | none => cases hf
    | some g =>
      simp only [dispatch, initChoice] at hf
      split at hf
      · cases hf
      · cases hf; exact origin.2 g rfl

/-- Joint non-vacuity includes a PRESENT function and a successful probe. -/
theorem symbol_links_satisfiable :
    ∃ (expected : Bool) (cached : Cache Bool) (resolved : Option Bool)
      (probe : Bool → Probe),
      PV_ROWS10B_Link_SymbolOrigin expected cached resolved ∧
      dispatch cached resolved probe = .callable expected := by
  refine ⟨false, .cold, some false, fun _ => ⟨0, 0⟩, ?_, ?_⟩
  · constructor
    · intro f h; cases h
    · intro f h; cases h; rfl
  · rfl

/-- A successful zero-byte probe gives NO symbol identity guarantee. This
refutes a proposed source-binding shortcut, not honest-run privacy. -/
theorem probe_not_symbol_binding :
    dispatch (.cold : Cache Bool) (some true) (fun _ => ⟨0, 0⟩) = .callable true ∧
    ¬ PV_ROWS10B_Link_SymbolOrigin false (.cold : Cache Bool) (some true) := by
  constructor
  · rfl
  · intro h
    have impossible := h.2 true rfl
    cases impossible

theorem cached_pointer_not_reprobed {Fn : Type} (f : Fn)
    (resolved : Option Fn) (probe : Fn → Probe) :
    dispatch (.callable f) resolved probe = .callable f := rfl

theorem probe_eio_keeps_pointer {Fn : Type} (f : Fn) :
    dispatch .cold (some f) (fun _ => ⟨-1, 5⟩) = .callable f := by rfl

theorem probe_enosys_falls_back {Fn : Type} (f : Fn) :
    dispatch .cold (some f) (fun _ => ⟨-1, 38⟩) = .unavailable := by rfl

theorem probe_eperm_falls_back {Fn : Type} (f : Fn) :
    dispatch .cold (some f) (fun _ => ⟨-1, 1⟩) = .unavailable := by rfl
#print axioms selected_origin
#print axioms symbol_links_satisfiable
#print axioms probe_not_symbol_binding
#print axioms cached_pointer_not_reprobed
#print axioms probe_eio_keeps_pointer
#print axioms probe_enosys_falls_back
#print axioms probe_eperm_falls_back
end R1Z.PV_ROWS10B_Dispatch
