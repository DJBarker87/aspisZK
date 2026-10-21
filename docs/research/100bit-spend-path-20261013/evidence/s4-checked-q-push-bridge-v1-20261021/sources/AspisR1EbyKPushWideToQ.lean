import Aeneas
import EbyKPushExplicitTypesV1
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1EbyKPushWideToQ

abbrev Wide := AspisR1EbyKPushCutV3.field.wide_exact.WideExact
abbrev Q := AspisR1EbyKPushCutV3.fast_pairing.canonical.Q

def toLimbs (self : Wide) : Result (Array Std.U32 8#usize) := do
  let i := self.c0.c0.a
  let i1 := self.c0.c0.b
  let i2 := self.c0.c1.a
  let i3 := self.c0.c1.b
  let i4 := self.c1.c0.a
  let i5 := self.c1.c0.b
  let i6 := self.c1.c1.a
  let i7 := self.c1.c1.b
  ok (Array.make 8#usize [i, i1, i2, i3, i4, i5, i6, i7])

def fromWide (value : Wide) : Result (Array Q 2#usize) := do
  let a ← toLimbs value
  let a1 ← Array.index_usize a 0#usize
  let b ← Array.index_usize a 1#usize
  let c ← Array.index_usize a 2#usize
  let d ← Array.index_usize a 3#usize
  let e ← Array.index_usize a 4#usize
  let f ← Array.index_usize a 5#usize
  let g ← Array.index_usize a 6#usize
  let h ← Array.index_usize a 7#usize
  ok (Array.make 2#usize [Array.make 4#usize [a1,b,c,d],
                            Array.make 4#usize [e,f,g,h]])

def qFromCoords (a b c d : Std.U32) : Q := Array.make 4#usize [a,b,c,d]
def pairFromCoords (i0 i1 i2 i3 i4 i5 i6 i7 : Std.U32) : Array Q 2#usize :=
  Array.make 2#usize [qFromCoords i0 i1 i2 i3, qFromCoords i4 i5 i6 i7]

theorem fromWide_coordinates (x : Wide) :
    fromWide x = .ok (pairFromCoords x.c0.c0.a x.c0.c0.b x.c0.c1.a x.c0.c1.b
      x.c1.c0.a x.c1.c0.b x.c1.c1.a x.c1.c1.b) := by
  simp [fromWide, toLimbs, pairFromCoords, qFromCoords,
    Array.index_usize, Array.make]

end AspisR1EbyKPushWideToQ

#print axioms AspisR1EbyKPushWideToQ.fromWide_coordinates
