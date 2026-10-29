import R1Z.PV_RDCD3_SliceRange194
import R1Z.PV_RDCD3_TryArray194
import R1Z.PV_RDCD3_Endian194
import R1Z.PV_RDCD3_FieldSource
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD3_BytesSource
open Aeneas Aeneas.Std Result
abbrev M := ProverRwFull.aspis_core.field.M31
abbrev C := ProverRwFull.aspis_core.field.CM31
abbrev Q := ProverRwFull.aspis_core.field.QM31
/-- Exact source branch on the decoded representative; no implicit reduction. -/
def scalar (bytes : Array U8 4#usize) : Option M :=
  let v := PV_RDCD3_Endian194.word bytes
  if v ≥ PV_RDCD3_FieldSource.aspis_core.field.P then none else some v

def component (bytes : List U8) (start stop : Nat) : Result (Option M) := do
  let part ← PV_RDCD3_SliceRange194.index bytes start stop
  match PV_RDCD3_TryArray194.into 4#usize part with
  | none => .ok none
  | some part => .ok (scalar part)

/-- CM31 source order: slice/try_into/decode a, short circuit on None, then b.
No eager length-eight check is introduced. -/
def cm (bytes : List U8) : Result (Option C) := do
  let a ← component bytes 0 4
  match a with
  | none => .ok none
  | some a => do
    let b ← component bytes 4 8
    match b with
    | none => .ok none
    | some b => .ok (some ⟨a,b⟩)

/-- QM31 source order: take first half, parse and short circuit, only then take
second half. This is an owned draft over backing bytes, not edited extraction. -/
def qm (bytes : List U8) : Result (Option Q) := do
  let left ← PV_RDCD3_SliceRange194.index bytes 0 8
  let c0 ← cm left
  match c0 with
  | none => .ok none
  | some c0 => do
    let right ← PV_RDCD3_SliceRange194.index bytes 8 16
    let c1 ← cm right
    match c1 with
    | none => .ok none
    | some c1 => .ok (some ⟨c0,c1⟩)

theorem scalar_binding (bytes : Array U8 4#usize) :
    scalar bytes = (let v := core.num.U32.from_le_bytes bytes
      if v ≥ PV_RDCD3_FieldSource.aspis_core.field.P then none else some v) := by
  rw [scalar,PV_RDCD3_Endian194.binding]

#print axioms scalar_binding
end R1Z.PV_RDCD3_BytesSource
