import NMX_LEFirst
set_option autoImplicit false
namespace NMX_U64Layout
open Aeneas Aeneas.Std AdapterRw
/-- Eight small symbolic byte cuts. The sparse zero-width terminal is reduced
before the recursive byte definition can create irrelevant terms. -/
theorem value (x : U64) : (core.num.U64.to_le_bytes x).val =
 [⟨(x.bv).setWidth 8⟩,
  ⟨((x.bv >>> 8).setWidth 56).setWidth 8⟩,
  ⟨(((x.bv >>> 8).setWidth 56 >>> 8).setWidth 48).setWidth 8⟩,
  ⟨((((x.bv >>> 8).setWidth 56 >>> 8).setWidth 48 >>> 8).setWidth 40).setWidth 8⟩,
  ⟨(((((x.bv >>> 8).setWidth 56 >>> 8).setWidth 48 >>> 8).setWidth 40 >>> 8).setWidth 32).setWidth 8⟩,
  ⟨((((((x.bv >>> 8).setWidth 56 >>> 8).setWidth 48 >>> 8).setWidth 40 >>> 8).setWidth 32 >>> 8).setWidth 24).setWidth 8⟩,
  ⟨(((((((x.bv >>> 8).setWidth 56 >>> 8).setWidth 48 >>> 8).setWidth 40 >>> 8).setWidth 32 >>> 8).setWidth 24 >>> 8).setWidth 16).setWidth 8⟩,
  ⟨((((((((x.bv >>> 8).setWidth 56 >>> 8).setWidth 48 >>> 8).setWidth 40 >>> 8).setWidth 32 >>> 8).setWidth 24 >>> 8).setWidth 16 >>> 8).setWidth 8).setWidth 8⟩] := by
 change x.bv.toLEBytes.map (fun v => (⟨v⟩ : U8)) = _
 rw [NMX_LEFirst.step _ (by decide)]
 rw [NMX_LEFirst.step _ (by decide)]
 rw [NMX_LEFirst.step _ (by decide)]
 rw [NMX_LEFirst.step _ (by decide)]
 rw [NMX_LEFirst.step _ (by decide)]
 rw [NMX_LEFirst.step _ (by decide)]
 rw [NMX_LEFirst.step _ (by decide)]
 rw [NMX_LEFirst.step _ (by decide)]
 rw [BitVec.toLEBytes.eq_1]
 rfl

#print axioms value
end NMX_U64Layout
