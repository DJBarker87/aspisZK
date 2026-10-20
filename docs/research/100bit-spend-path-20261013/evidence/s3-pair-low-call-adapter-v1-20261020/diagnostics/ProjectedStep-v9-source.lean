import S3PairLowCallLowStepV1
import S3PairLowCallOperationMapV1

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1PairLowCallCut

open AspisR1S3PowersLowEntryCanonicalV1

theorem closure_pair_let_eq {C} (p : weights.s2_twofold_low_array.closure)
    (f : Array field.WideExact 4#usize → Array field.WideExact 4#usize → C) :
    (let (a, b) := p; f a b) = f p.1 p.2 := by
  change (let (a, b) :=
      (p : Array field.WideExact 4#usize × Array field.WideExact 4#usize);
      f a b) = f p.1 p.2
  cases p
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
  unfold weights.s2_twofold_low_array.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
  simp only [closure_pair_let_eq]
  simp only [HMod.hMod, HDiv.hDiv, hmod, hdiv, bind_tc_ok]
  rw [hpermL]
  simp only [bind_tc_ok]
  rw [hreadL]
  simp only [bind_tc_ok]
  rw [hpermR]
  simp only [bind_tc_ok]
  rw [hreadR]
  simp only [bind_tc_ok, hscale]
  simp [lowStep, lowEntry, mulM31, actualFieldOps, LowFieldOps.wideMul,
    LowFieldOps.wideMulM31, hleft, hright, to_from_actual]

  end AspisR1PairLowCallCut
