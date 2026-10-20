import AspisR1EbyKDotPushSourceV1.Types
import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1EbyKDotPushSourceV1
@[global_simps, irreducible]
def fast_pairing.canonical.P : Std.U32 := 2147483647#u32

@[rust_loop_body]
def fast_pairing.canonical.Dot.push_loop.body
  (raw1 : Array Std.U64 4#usize) (iter : core.ops.range.Range Std.Usize)
  (self : fast_pairing.canonical.Dot) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) ×
    fast_pairing.canonical.Dot) fast_pairing.canonical.Dot)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done self)
  | some j =>
    let i ← Array.index_usize self.sums j
    let i1 ← Array.index_usize raw1 j
    let i2 ← lift (core.convert.num.FromU64U32.from fast_pairing.canonical.P)
    let i3 ← lift (i1 &&& i2)
    let i4 ← i1 >>> 31#i32
    let i5 ← lift (core.num.U64.wrapping_add i3 i4)
    let i6 ← lift (core.num.U64.wrapping_add i i5)
    let a ← Array.update self.sums j i6
    ok (cont (iter1, { sums := a }))

@[rust_loop]
def fast_pairing.canonical.Dot.push_loop
  (iter : core.ops.range.Range Std.Usize) (self : fast_pairing.canonical.Dot)
  (raw1 : Array Std.U64 4#usize) :
  Result fast_pairing.canonical.Dot
  := do
  loop
    (fun (iter1, self1) => fast_pairing.canonical.Dot.push_loop.body raw1 iter1
      self1)
    (iter, self)

def fast_pairing.canonical.Dot.push_raw
    (rawFn : fast_pairing.canonical.Q → fast_pairing.canonical.Q → Result (Array Std.U64 4#usize))
    (self : fast_pairing.canonical.Dot) (a b : fast_pairing.canonical.Q) : Result fast_pairing.canonical.Dot := do
  let raw1 ← rawFn a b
  fast_pairing.canonical.Dot.push_loop { start := 0#usize, «end» := 4#usize } self raw1

end AspisR1EbyKDotPushSourceV1
