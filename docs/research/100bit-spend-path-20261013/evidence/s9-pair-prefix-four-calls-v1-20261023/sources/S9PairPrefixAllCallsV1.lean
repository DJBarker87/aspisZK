import S9PairTermChildrenV1
import S9PairTermPrefixMapV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairPrefixAllCallsV1

abbrev PW := AspisR1S9PairCallerStepV1.field.WideExact
abbrev PQ := AspisR1S9PairCallerStepV1.field.QM31
abbrev PU := Std.Usize

def pairHigh (q41 q8 q12 : PQ) : Array PQ (4#usize) := Array.make 4#usize
  [AspisR1S9PairCallerStepV1.field.QM31.ONE,q41,q8,q12]

structure PairTermCallWitness (ap1 : Array PW (4#usize))
    (high : Array PQ (4#usize)) (i : PU) where
  perm : PU
  input : PW
  coefficient : PQ
  product : PW
  term : PW
  permRead : Array.index_usize _root_.AspisR1S9PairCallerStepV1.weights.PERM i = .ok perm
  inputRead : Array.index_usize ap1 perm = .ok input
  coefficientRead : Array.index_usize high i = .ok coefficient
  mixedSuccess : AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31 input coefficient = .ok product
  quarterSuccess : AspisR1S9PairCallerStepV1.field.WideExact.mul_m31 product
    _root_.AspisR1S9PairCallerStepV1.weights.QUARTER = .ok term

private theorem bind_success_inv {α β : Type}
    (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem pair_term_prefix_four_same_run_calls
    (ap1 : Array PW (4#usize)) (q41 q8 q12 : PQ)
    (perm3 : PU) (t0 t1 t2 t3 : PW)
    (h : AspisR1S9PairTermPrefixMapV1.pairTermPrefix ap1 q41 q8 q12 = .ok
      (perm3,(t0,t1,t2,t3))) :
    ∃ (w0 : PairTermCallWitness ap1 (pairHigh q41 q8 q12) 0#usize)
      (w1 : PairTermCallWitness ap1 (pairHigh q41 q8 q12) 1#usize)
      (w2 : PairTermCallWitness ap1 (pairHigh q41 q8 q12) 2#usize)
      (w3 : PairTermCallWitness ap1 (pairHigh q41 q8 q12) 3#usize),
      w0.term = t0 ∧ w1.term = t1 ∧ w2.term = t2 ∧ w3.term = t3 ∧
      w3.perm = perm3 := by
  let high := pairHigh q41 q8 q12
  have hc := h
  unfold AspisR1S9PairTermPrefixMapV1.pairTermPrefix at hc
  rcases bind_success_inv
    (AspisR1S9PairTermPrefixMapV1.pairTermAt ap1 high 0#usize) _ _ hc with
    ⟨r0,hr0,hc⟩
  rcases bind_success_inv
    (AspisR1S9PairTermPrefixMapV1.pairTermAt ap1 high 1#usize) _ _ hc with
    ⟨r1,hr1,hc⟩
  rcases bind_success_inv
    (AspisR1S9PairTermPrefixMapV1.pairTermAt ap1 high 2#usize) _ _ hc with
    ⟨r2,hr2,hc⟩
  rcases bind_success_inv
    (AspisR1S9PairTermPrefixMapV1.pairTermAt ap1 high 3#usize) _ _ hc with
    ⟨r3,hr3,hc⟩
  have hlast := Result.ok.inj hc
  have hperm : r3.1 = perm3 := congrArg Prod.fst hlast
  have ht0 : r0.2 = t0 := congrArg (fun z : PU × (PW × PW × PW × PW) => z.2.1) hlast
  have ht1 : r1.2 = t1 := congrArg (fun z : PU × (PW × PW × PW × PW) => z.2.2.1) hlast
  have ht2 : r2.2 = t2 := congrArg (fun z : PU × (PW × PW × PW × PW) => z.2.2.2.1) hlast
  have ht3 : r3.2 = t3 := congrArg (fun z : PU × (PW × PW × PW × PW) => z.2.2.2.2) hlast
  have hcall0 : AspisR1S9PairTermPrefixMapV1.pairTermAt ap1 high 0#usize = .ok (r0.1,t0) := by
    rw [← ht0]; exact hr0
  have hcall1 : AspisR1S9PairTermPrefixMapV1.pairTermAt ap1 high 1#usize = .ok (r1.1,t1) := by
    rw [← ht1]; exact hr1
  have hcall2 : AspisR1S9PairTermPrefixMapV1.pairTermAt ap1 high 2#usize = .ok (r2.1,t2) := by
    rw [← ht2]; exact hr2
  have hcall3 : AspisR1S9PairTermPrefixMapV1.pairTermAt ap1 high 3#usize = .ok (perm3,t3) := by
    rw [← hperm, ← ht3]; exact hr3
  obtain ⟨x0,a0,p0,hp0,hi0,hc0,hm0,hu0⟩ :=
    AspisR1S9PairTermChildrenV1.pair_term_at_success_children ap1 high 0#usize r0.1 t0 hcall0
  obtain ⟨x1,a1,p1,hp1,hi1,hc1,hm1,hu1⟩ :=
    AspisR1S9PairTermChildrenV1.pair_term_at_success_children ap1 high 1#usize r1.1 t1 hcall1
  obtain ⟨x2,a2,p2,hp2,hi2,hc2,hm2,hu2⟩ :=
    AspisR1S9PairTermChildrenV1.pair_term_at_success_children ap1 high 2#usize r2.1 t2 hcall2
  obtain ⟨x3,a3,p3,hp3,hi3,hc3,hm3,hu3⟩ :=
    AspisR1S9PairTermChildrenV1.pair_term_at_success_children ap1 high 3#usize perm3 t3 hcall3
  let w0 : PairTermCallWitness ap1 (pairHigh q41 q8 q12) 0#usize :=
    ⟨r0.1,x0,a0,p0,t0,hp0,hi0,hc0,hm0,hu0⟩
  let w1 : PairTermCallWitness ap1 (pairHigh q41 q8 q12) 1#usize :=
    ⟨r1.1,x1,a1,p1,t1,hp1,hi1,hc1,hm1,hu1⟩
  let w2 : PairTermCallWitness ap1 (pairHigh q41 q8 q12) 2#usize :=
    ⟨r2.1,x2,a2,p2,t2,hp2,hi2,hc2,hm2,hu2⟩
  let w3 : PairTermCallWitness ap1 (pairHigh q41 q8 q12) 3#usize :=
    ⟨perm3,x3,a3,p3,t3,hp3,hi3,hc3,hm3,hu3⟩
  exact ⟨w0,w1,w2,w3,rfl,rfl,rfl,rfl,rfl⟩

#print axioms pair_term_prefix_four_same_run_calls

end AspisR1S9PairPrefixAllCallsV1
