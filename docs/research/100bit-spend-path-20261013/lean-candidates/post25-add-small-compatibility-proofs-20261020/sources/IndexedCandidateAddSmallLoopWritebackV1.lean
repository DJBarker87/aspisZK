import AspisR1Post25SamplerStd.Funs

set_option autoImplicit false

open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1Post25Sampler

namespace AspisR1.ExtractedAddSmallLoopWritebackV1

variable [AspisR1Post25Sampler.StdOperationModel]

abbrev Iter := core.slice.iter.IterMut Std.U32

private theorem bindTripleKnown {A B C D : Type} (m : Result (A × B × C))
    (k : A → B → C → Result D) (a : A) (b : B) (c : C)
    (h : m = .ok (a, b, c)) :
    (do let x ← m; match x with | (x, y, z) => k x y z) = k a b c := by
  rw [h]
  rfl

/-- The arithmetic subprogram emitted in the `some digit` branch of the
source loop body. -/
def arithmeticStep (digit addend : Std.U32) : Result (Std.U32 × Std.U32) := do
  let i ← lift (core.convert.num.FromU64U32.from digit)
  let i1 ← lift (core.convert.num.FromU64U32.from addend)
  let sum ← i + i1
  let i2 ← lift (core.convert.num.FromU64U32.from field.P)
  let i3 ← sum % i2
  let digit1 ← lift (UScalar.cast .U32 i3)
  let i4 ← lift (core.convert.num.FromU64U32.from field.P)
  let i5 ← sum / i4
  let addend1 ← lift (UScalar.cast .U32 i5)
  ok (digit1, addend1)

def branchSome (iter1 : Iter) (back : Iter → Iter)
    (next_back : Iter → Option Std.U32 → Iter) (digit addend : Std.U32) :
    Result (ControlFlow (Iter × (Iter → Iter) × Std.U32)
      (Std.U32 × (Iter → Iter))) := do
  let i ← lift (core.convert.num.FromU64U32.from digit)
  let i1 ← lift (core.convert.num.FromU64U32.from addend)
  let sum ← i + i1
  let i2 ← lift (core.convert.num.FromU64U32.from field.P)
  let i3 ← sum % i2
  let digit1 ← lift (UScalar.cast .U32 i3)
  let i4 ← lift (core.convert.num.FromU64U32.from field.P)
  let i5 ← sum / i4
  let addend1 ← lift (UScalar.cast .U32 i5)
  ok (ControlFlow.cont (iter1,
    fun im => back (next_back im (some digit1)), addend1))

private theorem branchSome_factor (iter1 : Iter) (back : Iter → Iter)
    (next_back : Iter → Option Std.U32 → Iter) (digit addend : Std.U32) :
    branchSome iter1 back next_back digit addend = (do
      let pair ← arithmeticStep digit addend
      let digit1 := pair.1
      let addend1 := pair.2
      ok (ControlFlow.cont (iter1,
        fun im => back (next_back im (some digit1)), addend1))) := by
  simp only [branchSome, arithmeticStep, bind_assoc_eq, bind_tc_ok, Prod.fst, Prod.snd]

/-- Given the exact successful result of the source arithmetic pipeline, the
actual generated body retains the updated digit in its `next_back` closure. -/
theorem body_some_writeback
    (iter : Iter) (back : Iter → Iter) (addend digit : Std.U32)
    (iter1 : Iter) (nextBack : Iter → Option Std.U32 → Iter)
    (digitOut addendOut : Std.U32)
    (hnext : core.slice.iter.IteratorIterMut.next iter =
      .ok (some digit, iter1, nextBack))
    (harith : arithmeticStep digit addend = .ok (digitOut, addendOut)) :
    AspisR1Post25Sampler.sampler.add_small_base_p_loop.body iter back addend =
      .ok (.cont (iter1,
        fun im => back (nextBack im (some digitOut)), addendOut)) := by
  unfold AspisR1Post25Sampler.sampler.add_small_base_p_loop.body
  let k : Option Std.U32 → Iter → (Iter → Option Std.U32 → Iter) →
      Result (ControlFlow (Iter × (Iter → Iter) × Std.U32)
        (Std.U32 × (Iter → Iter))) := fun o it next_back =>
    match o with
    | none => ok (ControlFlow.done (addend, fun im => back (next_back im none)))
    | some d => branchSome it back next_back d addend
  change (do let (o, it, nb) ← core.slice.iter.IteratorIterMut.next iter
             k o it nb) = _
  rw [bindTripleKnown _ k _ _ _ hnext]
  dsimp [k]
  rw [branchSome_factor]
  rw [harith]
  rfl

#print axioms body_some_writeback

end AspisR1.ExtractedAddSmallLoopWritebackV1
