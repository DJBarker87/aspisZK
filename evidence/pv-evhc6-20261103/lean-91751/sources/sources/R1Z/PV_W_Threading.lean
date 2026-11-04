import Init
set_option autoImplicit false
namespace R1Z.PV_W_Threading

/-- Errors and divergence retain the effects already performed. This is not
ExceptT over StateT, which would erase the post-state on failure. -/
inductive Outcome (E A : Type) where
  | ok (value : A)
  | fail (error : E)
  | div
  deriving DecidableEq

structure Run (W C E A : Type) where
  outcome : Outcome E A
  world : W
  calls : List (W × C)

abbrev M (W C E A : Type) := W → Run W C E A
variable {W C E A B D : Type}

def lift (r : Outcome E A) : M W C E A := fun w => ⟨r,w,[]⟩
def bind (m : M W C E A) (k : A → M W C E B) : M W C E B := fun w =>
  let a := m w
  match a.outcome with
  | .ok x => let b := k x a.world; ⟨b.outcome,b.world,a.calls ++ b.calls⟩
  | .fail e => ⟨.fail e,a.world,a.calls⟩
  | .div => ⟨.div,a.world,a.calls⟩

/-- Any world-free callback lifts, but the theorem asserts purity of its
interpretation, not native purity of the callback's Rust referent. -/
def liftCallback {I : Type} (f : I → Outcome E A) (x : I) : M W C E A := lift (f x)

theorem lift_frame (r : Outcome E A) (w : W) :
    (lift (C := C) r w).world = w ∧ (lift (C := C) r w).calls = [] := ⟨rfl,rfl⟩

theorem lift_bind (r : Outcome E A) (k : A → Outcome E B) :
    bind (lift r) (fun a => lift (k a)) =
      (lift (C := C) (match r with | .ok a => k a | .fail e => .fail e | .div => .div) : M W C E B) := by
  cases r <;> rfl

theorem bind_ok (m : M W C E A) (k : A → M W C E B)
    (w : W) (a : A) (h : (m w).outcome = .ok a) :
    bind m k w = ⟨(k a (m w).world).outcome, (k a (m w).world).world,
      (m w).calls ++ (k a (m w).world).calls⟩ := by
  simp only [bind,h]

theorem bind_fail (m : M W C E A) (k : A → M W C E B)
    (w : W) (e : E) (h : (m w).outcome = .fail e) :
    bind m k w = ⟨.fail e,(m w).world,(m w).calls⟩ := by
  simp only [bind,h]

theorem bind_div (m : M W C E A) (k : A → M W C E B)
    (w : W) (h : (m w).outcome = .div) :
    bind m k w = ⟨.div,(m w).world,(m w).calls⟩ := by
  simp only [bind,h]

theorem bind_assoc (m : M W C E A) (k : A → M W C E B)
    (h : B → M W C E D) : bind (bind m k) h = bind m (fun a => bind (k a) h) := by
  funext w
  cases hm : (m w).outcome with
  | fail e => simp only [bind,hm]
  | div => simp only [bind,hm]
  | ok a =>
    cases hk : (k a (m w).world).outcome <;>
      simp only [bind,hm,hk,List.append_assoc]

/-- Every call is recorded at its own pre-world, in execution order. -/
def emit (c : C) (step : W → Outcome E A × W) : M W C E A := fun w =>
  ⟨(step w).1,(step w).2,[(w,c)]⟩

inductive Threaded (step : W → C → W → Prop) : W → List (W × C) → W → Prop where
  | nil (w : W) : Threaded step w [] w
  | cons {w next last : W} {c : C} {cs : List (W × C)} :
      step w c next → Threaded step next cs last → Threaded step w ((w,c)::cs) last

theorem threaded_append {step : W → C → W → Prop} {w mid last : W}
    {xs ys : List (W × C)} (left : Threaded step w xs mid)
    (right : Threaded step mid ys last) : Threaded step w (xs ++ ys) last := by
  induction left with
  | nil => exact right
  | cons h _ ih => exact .cons h (ih right)

def Valid (step : W → C → W → Prop) (m : M W C E A) : Prop :=
  ∀ w, Threaded step w (m w).calls (m w).world

theorem valid_lift (step : W → C → W → Prop) (r : Outcome E A) :
    Valid step (lift r) := fun w => .nil w

theorem valid_emit (step : W → C → W → Prop) (c : C)
    (f : W → Outcome E A × W) (law : ∀ w, step w c (f w).2) :
    Valid step (emit c f) := fun w => .cons (law w) (.nil _)

/-- Named compositional threading law, including failure/divergence prefixes.
It applies to a caller only after its individual control-flow correspondence
has been proved; it is not that correspondence itself. -/
theorem valid_bind (step : W → C → W → Prop) (m : M W C E A)
    (k : A → M W C E B) (hm : Valid step m) (hk : ∀ a, Valid step (k a)) :
    Valid step (bind m k) := by
  intro w
  cases h : (m w).outcome with
  | ok a => rw [bind_ok m k w a h]; exact threaded_append (hm w) (hk a _)
  | fail e => rw [bind_fail m k w e h]; exact hm w
  | div => rw [bind_div m k w h]; exact hm w

/-- A pure lift cannot represent even one advancing effect. -/
theorem no_lift_advancing (m : M W C E A) (w : W) (h : (m w).world ≠ w) :
    ∀ r : Outcome E A, lift r w ≠ m w := by
  intro r eq
  exact h (congrArg Run.world eq).symm

/-- A post-hoc decoder of returned values cannot recover a call trace when
one and two calls have the same return. This does not exclude syntax-directed
sidecar interpretation, which must retain calls before evaluation erases them. -/
theorem no_trace_decoder (r : Outcome E A) (w : W) (c : C) :
    ¬ ∃ decode : Outcome E A → List (W × C),
      decode r = [(w,c)] ∧ decode r = [(w,c),(w,c)] := by
  intro ⟨decode,one,two⟩
  have lengths := congrArg List.length (one.symm.trans two)
  exact (by decide : (1 : Nat) ≠ 2) lengths

#print axioms bind_assoc
#print axioms lift_frame
#print axioms lift_bind
#print axioms bind_ok
#print axioms bind_fail
#print axioms bind_div
#print axioms threaded_append
#print axioms valid_lift
#print axioms valid_emit
#print axioms valid_bind
#print axioms no_lift_advancing
#print axioms no_trace_decoder
end R1Z.PV_W_Threading
