import NCA_InactiveModel
import KMX_CopyMeaning
set_option autoImplicit false
namespace AspisR1.NCA_SerializerWindow
open Aeneas Aeneas.Std

/-- Full-carrier byte law matched by the arbitrary-prestate native zip step.
All unselected bytes are retained on this same 32-byte array. -/
theorem frame (out : Array U8 32#usize) (limb : U32) (i j : Nat)
    (window : i<8) (index : j<32) :
    (out.setSlice! (4*i) (core.num.U32.to_le_bytes limb).val).val[j]! =
      if 4*i ≤ j ∧ j<4*i+4 then
        (core.num.U32.to_le_bytes limb).val[j-4*i]! else out.val[j]! := by
  have length := (core.num.U32.to_le_bytes limb).property
  change (core.num.U32.to_le_bytes limb).val.length=4 at length
  by_cases inside : 4*i ≤ j ∧ j<4*i+4
  · rw [if_pos inside]
    have mid := Array.setSlice!_getElem!_middle out
      (core.num.U32.to_le_bytes limb).val (4*i) j (by scalar_tac)
    simpa only [Array.getElem!_Nat_eq] using mid
  · rw [if_neg inside]
    by_cases early : j<4*i
    · simpa only [Array.getElem!_Nat_eq] using
        Array.setSlice!_getElem!_prefix out (core.num.U32.to_le_bytes limb).val (4*i) j early
    · have late : 4*i+(core.num.U32.to_le_bytes limb).val.length≤j := by omega
      simpa only [Array.getElem!_Nat_eq] using
        Array.setSlice!_getElem!_suffix out (core.num.U32.to_le_bytes limb).val (4*i) j late

/-- Reuse the existing exact mutable-iterator induction; no eight-step reduction.
This theorem retains its complete source carrier and continuation. -/
theorem induction (x : AspisR1WideToBytesSource.field.wide_exact.WideExact)
    (n : Nat) (bound : n≤8) (z : P6ToBytes.Steps.Zip) :
    P6ToBytes.OutputInvariant.zipSource ((P6ToBytes.StateInvariant.stateAt x n).2 z) =
      P6ToBytes.OutputInvariant.painted x n (P6ToBytes.OutputInvariant.zipSource z) :=
  P6ToBytes.OutputInvariant.stateAt_paints x n bound z

#print axioms frame
#print axioms induction
end AspisR1.NCA_SerializerWindow
