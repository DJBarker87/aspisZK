import S3PairLowCallLowStepV1
import S3PairLowCallOperationMapV1

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1PairLowCallCut

open AspisR1S3PowersLowEntryCanonicalV1

theorem call_mut_read_form (ops : LowFieldOps)
    (c : weights.s2_twofold_low_array.closure) (i : Usize) :
    weights.s2_twofold_low_array.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
      ops c i =
      (do
        let r ← UScalar.rem i 4#usize
        let p ← Array.index_usize weights.PERM r
        let x ← Array.index_usize c.1 p
        let d ← UScalar.div i 4#usize
        let q ← Array.index_usize weights.PERM d
        let y ← Array.index_usize c.2 q
        let xy ← ops.wideMul x y
        let scale ← ops.m31Mul weights.QUARTER weights.QUARTER
        let out ← ops.wideMulM31 xy scale
        ok (out,c)) := by
  cases c
  rfl

/-! The following lemma isolates the arithmetic part of the callback
simulation.  Its read premises are discharged from the actual `%`, `/`, and
`Array.index_usize` specifications in the next theorem; they are not field
operation assumptions. -/
theorem projected_call_mut_eq_lowStep_of_reads
    (c : weights.s2_twofold_low_array.closure)
    (i r d p q : Std.Usize)
    (x y : field.WideExact)
    (s : field.M31)
    (hmod : UScalar.rem i (4#usize) = .ok r)
    (hdiv : UScalar.div i (4#usize) = .ok d)
    (hpermL : weights.PERM.index_usize r = .ok p)
    (hpermR : weights.PERM.index_usize d = .ok q)
    (hreadL : c.1.index_usize p = .ok x)
    (hreadR : c.2.index_usize q = .ok y)
    (hr : r.val = i.val % 4)
    (hd : d.val = i.val / 4)
    (hp : p.val = lowPerm r.val)
    (hq : q.val = lowPerm d.val)
    (hleft : (closureToLowInputs c).1.getD (lowPerm (i.val % 4))
        AspisR1CurrentPowers.field.WideExact.ONE = generatedToPower x)
    (hright : (closureToLowInputs c).2.getD (lowPerm (i.val / 4))
        AspisR1CurrentPowers.field.WideExact.ONE = generatedToPower y)
    (hscale : actualFieldOps.m31Mul weights.QUARTER weights.QUARTER = .ok s) :
    (do
      let (value, next) ←
        weights.s2_twofold_low_array.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
          actualFieldOps c i
      .ok (toActualS value, closureToLowInputs next)) =
      lowStep s (closureToLowInputs c) i.val := by
  rw [call_mut_read_form]
  simp only [hmod,bind_tc_ok,hpermL,hreadL,hdiv,hpermR,hreadR]
  simp only [hscale]
  simp [lowStep, lowEntry, mulM31, actualFieldOps,
    hleft, hright, to_from_actual]

#print axioms call_mut_read_form
#print axioms projected_call_mut_eq_lowStep_of_reads

  end AspisR1PairLowCallCut
