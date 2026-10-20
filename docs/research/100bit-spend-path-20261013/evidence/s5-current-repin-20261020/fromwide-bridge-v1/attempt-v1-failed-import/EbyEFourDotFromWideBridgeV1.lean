import AspisR1EbyEFourDotSourceStepV1
import AspisR1EbyKPushWideToQ

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1EbyEFourDotFromWideBridgeV1

abbrev SourceWide := AspisR1EbyEDotCutV1.field.wide_exact.WideExact
abbrev SourceQ := AspisR1EbyEDotCutV1.fast_pairing.canonical.Q
abbrev PushWide := AspisR1EbyKPushWideToQ.Wide

/-- The fieldwise carrier map from the EbyE cut to the already checked EbyK
wide carrier. -/
def toPushWide (x : SourceWide) : PushWide :=
  ⟨⟨⟨x.c0.c0.a, x.c0.c0.b⟩, ⟨x.c0.c1.a, x.c0.c1.b⟩⟩,
    ⟨⟨x.c1.c0.a, x.c1.c0.b⟩, ⟨x.c1.c1.a, x.c1.c1.b⟩⟩⟩

def sourceToLimbs (self : SourceWide) : Result (Array Std.U32 8#usize) := do
  let i := self.c0.c0.a
  let i1 := self.c0.c0.b
  let i2 := self.c0.c1.a
  let i3 := self.c0.c1.b
  let i4 := self.c1.c0.a
  let i5 := self.c1.c0.b
  let i6 := self.c1.c1.a
  let i7 := self.c1.c1.b
  ok (Array.make 8#usize [i, i1, i2, i3, i4, i5, i6, i7])

/-- Verbatim source-shaped body of the extracted `Q::from_wide`, over the
selected source cut types. -/
def sourceFromWide (value : SourceWide) : Result (Array SourceQ 2#usize) := do
  let a ← sourceToLimbs value
  let a1 ← Array.index_usize a 0#usize
  let b ← Array.index_usize a 1#usize
  let c ← Array.index_usize a 2#usize
  let d ← Array.index_usize a 3#usize
  let e ← Array.index_usize a 4#usize
  let f ← Array.index_usize a 5#usize
  let g ← Array.index_usize a 6#usize
  let h ← Array.index_usize a 7#usize
  ok (Array.make 2#usize [Array.make 4#usize [ a1, b, c, d ],
                            Array.make 4#usize [ e, f, g, h ]])

theorem toPushWide_fields (x : SourceWide) :
    (toPushWide x).c0.c0.a = x.c0.c0.a ∧
    (toPushWide x).c0.c0.b = x.c0.c0.b ∧
    (toPushWide x).c0.c1.a = x.c0.c1.a ∧
    (toPushWide x).c0.c1.b = x.c0.c1.b ∧
    (toPushWide x).c1.c0.a = x.c1.c0.a ∧
    (toPushWide x).c1.c0.b = x.c1.c0.b ∧
    (toPushWide x).c1.c1.a = x.c1.c1.a ∧
    (toPushWide x).c1.c1.b = x.c1.c1.b := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem sourceFromWide_eq_checked_fromWide (x : SourceWide) :
    sourceFromWide x = AspisR1EbyKPushWideToQ.fromWide (toPushWide x) := by
  rw [AspisR1EbyKPushWideToQ.fromWide_coordinates]
  simp [sourceFromWide, sourceToLimbs, toPushWide,
    AspisR1EbyKPushWideToQ.pairFromCoords,
    AspisR1EbyKPushWideToQ.qFromCoords,
    Array.index_usize, Array.make]

#print axioms toPushWide_fields
#print axioms sourceFromWide_eq_checked_fromWide

end AspisR1EbyEFourDotFromWideBridgeV1
