import Aeneas
import AspisR1SelectedMaskProbe.Types
import AspisR1SelectedMaskProbe.FunsExternal
import TerminalV4TerminalPartsArithmeticJoinChunk13V2

open Aeneas Aeneas.Std Result
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace AspisR1SelectedMaskProbe.TerminalV4CurrentArithmeticContract

abbrev QM := field.QM31

/-- Exactness premises for the operations called by the current generated
terminal-parts suffix. They mention the actual chunk-local operations. -/
structure Laws (K : Type) [Add K] [Sub K] [Mul K] where
  decode : QM → K
  canonical : QM → Prop
  add_exact : ∀ x y, canonical x → canonical y →
    ∃ z, field.QM31.add x y = .ok z ∧ canonical z ∧ decode z = decode x + decode y
  sub_exact : ∀ x y, canonical x → canonical y →
    ∃ z, field.QM31.sub x y = .ok z ∧ canonical z ∧ decode z = decode x - decode y
  mul_exact : ∀ x y, canonical x → canonical y →
    ∃ z, field.QM31.mul x y = .ok z ∧ canonical z ∧ decode z = decode x * decode y
  one_canonical : canonical field.QM31.ONE
  one_decode : decode field.QM31.ONE = 1

def run (q composition h1Z copyActive mu : QM) : Result QM := do
  let q1 ← field.QM31.mul q composition
  let q2 ← field.QM31.mul mu h1Z
  let q3 ← field.QM31.add q1 q2
  let q4 ← field.QM31.mul mu mu
  let q5 ← field.QM31.sub field.QM31.ONE copyActive
  let q6 ← field.QM31.mul q5 h1Z
  let q7 ← field.QM31.mul q4 q6
  field.QM31.add q3 q7

theorem run_exact {K : Type} [Add K] [Sub K] [Mul K]
    (laws : Laws K) (q composition h1Z copyActive mu : QM)
    (hq : laws.canonical q) (hc : laws.canonical composition)
    (hh : laws.canonical h1Z) (ha : laws.canonical copyActive)
    (hm : laws.canonical mu) :
    ∃ out, run q composition h1Z copyActive mu = .ok out ∧
      laws.canonical out ∧
      laws.decode out =
        (laws.decode q * laws.decode composition + laws.decode mu * laws.decode h1Z) +
        (laws.decode mu * laws.decode mu) *
          ((1 - laws.decode copyActive) * laws.decode h1Z) := by
  obtain ⟨q1, hq1, hc1, vq1⟩ := laws.mul_exact q composition hq hc
  obtain ⟨q2, hq2, hc2, vq2⟩ := laws.mul_exact mu h1Z hm hh
  obtain ⟨q3, hq3, hc3, vq3⟩ := laws.add_exact q1 q2 hc1 hc2
  obtain ⟨q4, hq4, hc4, vq4⟩ := laws.mul_exact mu mu hm hm
  obtain ⟨q5, hq5, hc5, vq5⟩ := laws.sub_exact field.QM31.ONE copyActive laws.one_canonical ha
  obtain ⟨q6, hq6, hc6, vq6⟩ := laws.mul_exact q5 h1Z hc5 hh
  obtain ⟨q7, hq7, hc7, vq7⟩ := laws.mul_exact q4 q6 hc4 hc6
  obtain ⟨out, hout, hcout, vout⟩ := laws.add_exact q3 q7 hc3 hc7
  refine ⟨out, ?_, hcout, ?_⟩
  · simp only [run, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hout, bind_tc_ok]
  · rw [vout, vq3, vq1, vq2, vq7, vq4, vq6, vq5, laws.one_decode]

#print axioms run_exact
end AspisR1SelectedMaskProbe.TerminalV4CurrentArithmeticContract
