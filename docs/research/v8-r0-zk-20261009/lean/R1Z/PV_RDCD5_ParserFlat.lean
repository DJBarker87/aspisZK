import R1Z.PV_RDCD5_ParserWindows
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD5_ParserFlat
open Aeneas Aeneas.Std Result PV_RDCD4_BytesSource

/-- Absolute component offsets, preserving a's None short circuit before b. -/
def cmAt (bytes : List U8) (base : Nat) : Result (Option C) := do
  let a ← component bytes (base+0) (base+(0+4))
  match a with
  | none => ok none
  | some a => do
    let b ← component bytes (base+4) (base+(4+4))
    match b with
    | none => ok none
    | some b => ok (some ⟨a,b⟩)

/-- The bounded borrowed window and absolute backing-byte windows feed the
same decoders, including their complete Result and short-circuit behavior. -/
theorem cm_window (bytes : List U8) (base : Nat) (hb : base+8 ≤ bytes.length) :
    cm (PV_RDCD4_SliceRange194.window bytes base (base+8)) = cmAt bytes base := by
  unfold cm cmAt
  rw [PV_RDCD5_ParserWindows.component_window bytes base 0 (by omega) hb]
  apply congrArg (fun f : Option M → Result (Option C) =>
    component bytes (base+0) (base+(0+4)) >>= f)
  funext a
  cases a with
  | none => rfl
  | some a =>
    dsimp only
    rw [PV_RDCD5_ParserWindows.component_window bytes base 4 (by omega) hb]

#print axioms cm_window
end R1Z.PV_RDCD5_ParserFlat
