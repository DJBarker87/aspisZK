import Aeneas
open Aeneas Aeneas.Std Result

namespace AspisR1FastDotsFixedCallTraceV1

abbrev Usize := Std.Usize

/-- A source-shaped adapter for the emitted four_dots_fixed suffix.  The
    pre input is exactly the generated slice-prefix/try_from/unwrap chain;
    one is the generated helper call, supplied explicitly to avoid importing
    its external templates into this call-flow proof. -/
def fixedCalls {Q G W : Type} (pre : Result Q)
    (one : Q → G → Usize → Result W) (g : G) : Result (Array W 4#usize) := do
  let q1 ← pre
  let we ← one q1 g 0#usize
  let we1 ← one q1 g 1#usize
  let we2 ← one q1 g 2#usize
  let we3 ← one q1 g 3#usize
  ok (Array.make 4#usize [we, we1, we2, we3])

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem successful_call_trace {Q G W : Type} (pre : Result Q)
    (one : Q → G → Usize → Result W) (g : G) (out : Array W 4#usize)
    (h : fixedCalls pre one g = .ok out) :
    ∃ q1 w0 w1 w2 w3,
      pre = .ok q1 ∧
      one q1 g 0#usize = .ok w0 ∧
      one q1 g 1#usize = .ok w1 ∧
      one q1 g 2#usize = .ok w2 ∧
      one q1 g 3#usize = .ok w3 ∧
      out = Array.make 4#usize [w0, w1, w2, w3] := by
  unfold fixedCalls at h
  obtain ⟨q1, hpre, hrest⟩ := bind_success pre (fun q1 => do
    let we ← one q1 g 0#usize
    let we1 ← one q1 g 1#usize
    let we2 ← one q1 g 2#usize
    let we3 ← one q1 g 3#usize
    ok (Array.make 4#usize [we, we1, we2, we3])) out h
  obtain ⟨w0, h0, hrest⟩ := bind_success (one q1 g 0#usize) (fun we => do
    let we1 ← one q1 g 1#usize
    let we2 ← one q1 g 2#usize
    let we3 ← one q1 g 3#usize
    ok (Array.make 4#usize [we, we1, we2, we3])) out hrest
  obtain ⟨w1, h1, hrest⟩ := bind_success (one q1 g 1#usize) (fun we1 => do
    let we2 ← one q1 g 2#usize
    let we3 ← one q1 g 3#usize
    ok (Array.make 4#usize [w0, we1, we2, we3])) out hrest
  obtain ⟨w2, h2, hrest⟩ := bind_success (one q1 g 2#usize) (fun we2 => do
    let we3 ← one q1 g 3#usize
    ok (Array.make 4#usize [w0, w1, we2, we3])) out hrest
  obtain ⟨w3, h3, hlast⟩ := bind_success (one q1 g 3#usize)
    (fun we3 => .ok (Array.make 4#usize [w0, w1, w2, we3])) out hrest
  have hout : Array.make 4#usize [w0, w1, w2, w3] = out :=
    Result.ok.inj hlast
  exact ⟨q1, w0, w1, w2, w3, hpre, h0, h1, h2, h3, hout.symm⟩

#print axioms successful_call_trace
end AspisR1FastDotsFixedCallTraceV1
