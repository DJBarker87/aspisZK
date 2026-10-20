/-! A generic exact arithmetic tail used to port the selected QM31 source proof
without importing the legacy generated `Funs` owner. Operation-specific success,
canonicality, and value lemmas are explicit inputs to this chain. -/

structure TerminalV4ExactOps (Q K : Type) [Add K] [Sub K] [Mul K] where
  one : Q
  canonical : Q → Prop
  decode : Q → K
  add : Q → Q → Option Q
  sub : Q → Q → Option Q
  mul : Q → Q → Option Q
  add_exact : ∀ x y, canonical x → canonical y →
    ∃ z, add x y = some z ∧ canonical z ∧ decode z = decode x + decode y
  sub_exact : ∀ x y, canonical x → canonical y →
    ∃ z, sub x y = some z ∧ canonical z ∧ decode z = decode x - decode y
  mul_exact : ∀ x y, canonical x → canonical y →
    ∃ z, mul x y = some z ∧ canonical z ∧ decode z = decode x * decode y

namespace TerminalV4ExactOps

variable {Q K : Type} [Add K] [Sub K] [Mul K]

def run (op : TerminalV4ExactOps Q K) (q composition h1Z copyActive mu : Q) : Option Q := do
  let q1 ← op.mul q composition
  let q2 ← op.mul mu h1Z
  let q3 ← op.add q1 q2
  let q4 ← op.mul mu mu
  let q5 ← op.sub op.one copyActive
  let q6 ← op.mul q5 h1Z
  let q7 ← op.mul q4 q6
  op.add q3 q7

theorem run_exact (op : TerminalV4ExactOps Q K)
    (q composition h1Z copyActive mu : Q)
    (hq : op.canonical q) (hc : op.canonical composition)
    (hh : op.canonical h1Z) (ha : op.canonical copyActive)
    (hm : op.canonical mu) (hone : op.canonical op.one) :
    ∃ out, run op q composition h1Z copyActive mu = some out ∧
      op.canonical out ∧
      op.decode out =
        (op.decode q * op.decode composition + op.decode mu * op.decode h1Z) +
        (op.decode mu * op.decode mu) *
          ((op.decode op.one - op.decode copyActive) * op.decode h1Z) := by
  obtain ⟨q1, hq1, hc1, vq1⟩ := op.mul_exact q composition hq hc
  obtain ⟨q2, hq2, hc2, vq2⟩ := op.mul_exact mu h1Z hm hh
  obtain ⟨q3, hq3, hc3, vq3⟩ := op.add_exact q1 q2 hc1 hc2
  obtain ⟨q4, hq4, hc4, vq4⟩ := op.mul_exact mu mu hm hm
  obtain ⟨q5, hq5, hc5, vq5⟩ := op.sub_exact op.one copyActive hone ha
  obtain ⟨q6, hq6, hc6, vq6⟩ := op.mul_exact q5 h1Z hc5 hh
  obtain ⟨q7, hq7, hc7, vq7⟩ := op.mul_exact q4 q6 hc4 hc6
  obtain ⟨out, hout, hcout, vout⟩ := op.add_exact q3 q7 hc3 hc7
  refine ⟨out, ?_, hcout, ?_⟩
  · simp [run, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hout]
  · rw [vout, vq3, vq1, vq2, vq7, vq4, vq6, vq5]

#print axioms run_exact
end TerminalV4ExactOps
