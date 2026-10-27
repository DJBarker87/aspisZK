import PoseidonPreparedChannelStep
import ExtractedMaskM31AddSub

set_option autoImplicit false
namespace AspisR1PoseidonPreparedChannelGeneratedStep
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

abbrev U32 := UScalar UScalarTy.U32
abbrev U64 := UScalar UScalarTy.U64
abbrev P : Nat := 2147483647

/-- Exact scalar code at each visited channel in the 04fc qmsum3 inner loop.
This keeps the generated checked casts, multiplication and accumulation in
scope, while reusing the focused arithmetic result for its semantics. -/
def generatedChannelUpdate (left right : field.M31) (acc : U64) : Result U64 := do
  let i ← lift (UScalar.cast .U64 left)
  let i1 ← lift (UScalar.cast .U64 right)
  let i2 ← i * i1
  acc + i2

theorem generatedChannelUpdate_success
    (left right : field.M31) (acc : U64)
    (hleft : left.val < P) (hright : right.val < P)
    (hacc : acc.val ≤ 2 * (P - 1) ^ 2) :
    ∃ out : U64,
      generatedChannelUpdate left right acc = .ok out ∧
      out.val = acc.val + left.val * right.val := by
  obtain ⟨out, hrun, hval⟩ :=
    AspisR1PoseidonPreparedChannelStep.sourceChannelProductAdd_success
      left right acc hleft hright hacc
  have hrun' : generatedChannelUpdate left right acc = .ok out := by
    change generatedChannelUpdate left right acc = .ok out at hrun
    exact hrun
  exact ⟨out, hrun', hval⟩

#print axioms generatedChannelUpdate_success
end AspisR1PoseidonPreparedChannelGeneratedStep
