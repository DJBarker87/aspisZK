import AspisR1S9HelperP6.Funs
import KpowersP6SuccessTraceV1
import S4FromFnP6GeneratedInterface
import S2LibraFactoredIdentity

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1S9HelperP6PowerSemanticsV1

open AspisR1S9HelperP6
open AspisR1FromFnP6
open AspisR1FromFnP6Generated
open AspisR1S9HelperP6TraceV1

/-- Denotational interface needed to interpret the generated QM31 power
callback. These are hypotheses about an installed field implementation, not
axioms and not a claim that every `FieldOps` satisfies them. -/
structure QMSemantics (E : Type) [CommSemiring E] [FieldOps] where
  canonical : field.QM31 → Prop
  decode : field.QM31 → E
  one_canonical : canonical field.QM31.ONE
  decode_one : decode field.QM31.ONE = 1
  mul_success : ∀ a b z, canonical a → canonical b →
    FieldOps.qmMul a b = .ok z →
      canonical z ∧ decode z = decode a * decode b

variable {E : Type} [CommSemiring E] [FieldOps]
variable (sem : QMSemantics E)

/-- Invariant of the generated `kpowers` closure after `index` transitions. -/
def powerStateOK {N : Std.Usize} (x : field.QM31) (state : weights.kpowers.closure N)
    (index : Nat) : Prop :=
  sem.canonical state.1 ∧ sem.canonical state.2 ∧
    sem.decode state.2 = sem.decode x ∧
    sem.decode state.1 = sem.decode x ^ index

/-- One successful emitted callback step is exactly the old power as output
and the successful multiplication as the next closure's first component. -/
theorem kpowers_step_semantic {N : Std.Usize} {a q v : field.QM31}
    {index : Nat} {cursorU : Std.Usize}
    {next : (weights.kpowers.closure N × Std.Usize)}
    (ha : sem.canonical a) (hq : sem.canonical q)
    (hstep : fnMutStep
      (weights.kpowers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 N)
      ((a, q), cursorU) index = .ok (v, next)) :
    ∃ product,
      FieldOps.qmMul a q = .ok product ∧
      sem.canonical product ∧
      sem.decode product = sem.decode a * sem.decode q ∧
      v = a ∧ next.1 = (product, q) := by
  let cb := weights.kpowers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 N
  cases hm : FieldOps.qmMul a q with
  | fail e =>
      have hcall : cb.call_mut (a, q) cursorU = .fail e := by
        simp [cb,
          weights.kpowers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut,
          field.QM31.mul,
          weights.kpowers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut,
          hm]
      unfold fnMutStep at hstep
      rw [hcall] at hstep
      simp at hstep
  | div =>
      have hcall : cb.call_mut (a, q) cursorU = .div := by
        simp [cb,
          weights.kpowers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut,
          field.QM31.mul,
          hm]
      unfold fnMutStep at hstep
      rw [hcall] at hstep
      simp at hstep
  | ok product =>
      have hmul : FieldOps.qmMul a q = .ok product := hm
      cases hi : cursorU + 1#usize with
      | fail e =>
          have hcall : cb.call_mut (a, q) cursorU = .ok (a, (product, q)) := by
            simp [cb,
              weights.kpowers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut,
              field.QM31.mul, hm]
          unfold fnMutStep at hstep
          rw [hcall, hi] at hstep
          simp at hstep
      | div =>
          have hcall : cb.call_mut (a, q) cursorU = .ok (a, (product, q)) := by
            simp [cb,
              weights.kpowers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut,
              field.QM31.mul, hm]
          unfold fnMutStep at hstep
          rw [hcall, hi] at hstep
          simp at hstep
      | ok cursor' =>
          have hcall : cb.call_mut (a, q) cursorU = .ok (a, (product, q)) := by
            simp [cb,
              weights.kpowers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut,
              field.QM31.mul, hm]
          have hrun : fnMutStep
              cb
              ((a, q), cursorU) index = .ok (a, ((product, q), cursor')) := by
            unfold fnMutStep
            rw [hcall, hi]
            rfl
          have hout := Result.ok.inj (hrun.symm.trans hstep)
          rcases Prod.mk.inj hout with ⟨hv, hnext⟩
          have hfirst : next.1 = (product, q) := (congrArg Prod.fst hnext).symm
          exact ⟨product, rfl, (sem.mul_success a q product ha hq hmul).1,
            (sem.mul_success a q product ha hq hmul).2, hv.symm, hfirst⟩

/-- A successful trace for `kpowers` has the expected denotation at every
array index. The list/index bridge is explicit; this theorem does not assert a
Rust `core::array::from_fn` correspondence. -/
theorem kpowers_trace_values {N : Std.Usize} {x : field.QM31}
    {values : List field.QM31} {final : (weights.kpowers.closure N × Std.Usize)}
    (hx : sem.canonical x)
    (htrace : StatefulFromFnTrace
      (fnMutStep (weights.kpowers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 N))
      N.val 0 ((field.QM31.ONE, x), 0#usize) values final) :
    values.length = N.val ∧
      (∀ i < N.val, ∀ v, values[i]? = some v →
        sem.canonical v ∧ sem.decode v = sem.decode x ^ i) ∧
      powerStateOK sem x final.1 N.val := by
  have hinit : powerStateOK (N := N) sem x (field.QM31.ONE, x) 0 := by
    exact ⟨sem.one_canonical, hx, rfl, by rw [sem.decode_one, pow_zero]⟩
  have hpres : ∀ {count start state cursor vals fin},
      powerStateOK sem x state start →
      StatefulFromFnTrace
        (fnMutStep (weights.kpowers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 N))
        count start (state, cursor) vals fin →
      (∀ i < count, ∀ v, vals[i]? = some v →
        sem.canonical v ∧ sem.decode v = sem.decode x ^ (start + i)) ∧
      powerStateOK sem x fin.1 (start + count) := by
    intro count
    induction count with
    | zero =>
        intro start state cursor vals fin hstate htr
        cases htr
        constructor
        · intro i hi
          omega
        · simpa using hstate
    | succ count ih =>
        intro start state cursor vals fin hstate htr
        cases htr with
        | @call _ _ _ traceNext traceFinal value tail hcall htail =>
            rcases hstate with ⟨ha, hq, hqx, hpow⟩
            rcases state with ⟨a,q⟩
            obtain ⟨prod, hmul, hprodCan, hprodDecode, hvalue, hnextClosure⟩ :=
              kpowers_step_semantic sem ha hq hcall
            have hnext : traceNext.1 = (prod, q) := hnextClosure
            have hstepState : powerStateOK (N := N) sem x (prod, q) (start + 1) := by
              refine ⟨hprodCan, hq, hqx, ?_⟩
              rw [hprodDecode, hqx, hpow]
              simp [pow_succ]
            have hstateNext : powerStateOK sem x traceNext.1 (start + 1) := by
              simpa [hnext] using hstepState
            have hnextTrace := ih hstateNext htail
            constructor
            · intro i hi v hv
              by_cases hiz : i = 0
              · subst i
                have hv0 : value = v := Option.some.inj (by simpa using hv)
                rw [hvalue] at hv0
                subst v
                exact ⟨ha, hpow⟩
              · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hiz
                have hj : j < count := by omega
                have hv' : tail[j]? = some v := by simpa using hv
                obtain ⟨hcan, hdec⟩ := hnextTrace.1 j hj v hv'
                refine ⟨hcan, ?_⟩
                calc
                  sem.decode v = sem.decode x ^ (start + 1 + j) := hdec
                  _ = sem.decode x ^ (start + j.succ) := by congr 1 <;> omega
            · have hindex : start + 1 + count = start + (count + 1) := by omega
              rw [← hindex]
              exact hnextTrace.2
  have hmain := hpres hinit htrace
  refine ⟨statefulFromFnTrace_length htrace, ?_, ?_⟩
  · intro i hi v hv
    simpa using hmain.1 i hi v hv
  · simpa using hmain.2

/-- Direct consumer theorem for an actual successful generated `kpowers`
result: every returned array entry is the corresponding decoded power. -/
theorem kpowers_success_pointwise {N : Std.Usize} {x : field.QM31}
    {values : Array field.QM31 N}
    (hx : sem.canonical x)
    (h : weights.kpowers N x = .ok values) :
    ∀ i < N.val, ∀ v, values.val[i]? = some v →
      sem.canonical v ∧ sem.decode v = sem.decode x ^ i := by
  obtain ⟨final, htrace⟩ := kpowers_success_trace h
  exact (kpowers_trace_values sem hx htrace).2.1

#print axioms kpowers_step_semantic
#print axioms kpowers_trace_values
#print axioms kpowers_success_pointwise

end AspisR1S9HelperP6PowerSemanticsV1
