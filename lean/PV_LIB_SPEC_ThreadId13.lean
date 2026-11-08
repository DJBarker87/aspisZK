import PV_LIB_SPEC_ThreadWords12
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ThreadId13
open PV_STX_Machine PV_STX2_Syntax PV_EVHB_OwnerMachine PV_LIB_SPEC_D984
open PV_LIB_SPEC_ThreadWords12

/-- Adopted fc8808eb,17bd20 loads COUNTER at1b67b8;17bd30 tests max;
17bd36/17bd3a CAS last+1;17bd45 returns that NONZERO word. This is the
single successful CAS schedule, with no competing thread write during this
poll. Arbitrary interference/exhaustion are not certified by this model.
Unknown or exhausted memory remains an explicit gap, never wrapping to zero. -/
def counterOffset : Nat := 0x1b67b8

def value (bias : Nat) (w : OWNER) : Option (Nat × OWNER) := do
  let last ← read w (bias+counterOffset)
  if last.val+1 < 2^64 then
    pure (last.val+1,write w (bias+counterOffset) (last.val+1))
  else none

/-- All non-success full answers are retained. A successful native452 request
is computed from the real pre-memory, rather than the old constant2 marker. -/
def reply (bias : Nat) (w : OWNER) (r : Reply OWNER Event Data) :
    Option (Reply OWNER Event Data) :=
  match r.answer with
  | .returned (.ok _) => do
    let (id,changed) ← value bias w
    pure ⟨.returned (.ok (.number id)),
      {r.world with world := {r.world.world with memory := changed.world.memory}},r.events⟩
  | _ => some r

theorem stored_counter (w : OWNER) (bias : Nat) (last : Pointer)
    (bound : last.val+1 < 2^64) :
    value bias (write w (bias+counterOffset) last.val) =
      some (last.val+1,write (write w (bias+counterOffset) last.val)
        (bias+counterOffset) (last.val+1)) := by
  unfold value
  rw [read_written]
  exact if_pos bound

theorem other (bias : Nat) (w : OWNER) (r : Reply OWNER Event Data)
    (h : ∀ v, r.answer ≠ .returned (.ok v)) : reply bias w r = some r := by
  cases a : r.answer with
  | pending => simp only [reply,a]
  | fault f => simp only [reply,a]
  | returned result => cases result with
    | ok v => exact False.elim (h v a)
    | fail e => simp only [reply,a]
    | div => simp only [reply,a]

theorem successful_ghost (bias : Nat) (w : OWNER) (id : Nat) (changed : OWNER)
    (result : value bias w = some (id,changed)) :
    PV_LIB_SPEC_NativeRuntime.GhostFrame w changed := by
  unfold value at result
  cases loaded : read w (bias+counterOffset) with
  | none => simp only [loaded,Option.bind_none] at result; cases result
  | some last =>
    rw [loaded] at result
    change (if last.val+1 < 2^64 then
      some (last.val+1,write w (bias+counterOffset) (last.val+1))
      else none) = some (id,changed) at result
    split at result
    · cases result; exact ghost_write _ _ _
    · cases result

#print axioms counterOffset
#print axioms value
#print axioms reply
#print axioms stored_counter
#print axioms other
#print axioms successful_ghost
end PV_LIB_SPEC_ThreadId13
