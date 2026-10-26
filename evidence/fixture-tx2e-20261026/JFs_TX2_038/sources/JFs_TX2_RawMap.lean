import JFs_TX2_RawMath
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_RawMap
open Aeneas Aeneas.Std Result

def pack {α : Type} (a b c d : α) : Array α 4#usize := Array.make 4#usize [a,b,c,d]

theorem left (a b c d : U32) : core.array.Array.map
    FIo_QRaw.canonical.Q.raw.closure.Insts.CoreOpsFunctionFnMutTupleU32U64 (pack a b c d) ()=
      ok (pack (JFs_TX2_RawMath.extend a) (JFs_TX2_RawMath.extend b)
        (JFs_TX2_RawMath.extend c) (JFs_TX2_RawMath.extend d)) := by rfl

theorem right (a b c d : U32) : core.array.Array.map
    FIo_QRaw.canonical.Q.raw.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64 (pack a b c d) ()=
      ok (pack (JFs_TX2_RawMath.extend a) (JFs_TX2_RawMath.extend b)
        (JFs_TX2_RawMath.extend c) (JFs_TX2_RawMath.extend d)) := by rfl

theorem shape {α : Type} (xs : Array α 4#usize) : ∃ a b c d, xs=pack a b c d := by
  rcases xs with ⟨xs,h⟩
  change xs.length=4 at h
  cases xs with
  | nil => simp at h
  | cons a xs =>
    cases xs with
    | nil => simp at h
    | cons b xs =>
      cases xs with
      | nil => simp at h
      | cons c xs =>
        cases xs with
        | nil => simp at h
        | cons d xs =>
          cases xs with
          | nil => exact ⟨a,b,c,d,rfl⟩
          | cons e xs => simp at h

#print axioms left
#print axioms right
#print axioms shape
end AspisR1.JFs_TX2_RawMap
end
