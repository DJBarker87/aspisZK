
set_option maxHeartbeats 1000000 in
/-- P3b: fresh QM31.mul = gate QM31.mul as functions on ALL inputs. The gate first runs r24_canonical_mul: if any of the eight
    limbs is >= P it returns none and the gate runs the same Karatsuba chain as fresh (r24_none); otherwise it returns
    some result, and r24_canon + chain_spec + comp0..3 prove that result equals the chain output limb by limb. -/
theorem PRVEq.AspisR72Sampler.Funs.field.QM31.mul : @AspisR72Sampler.PRVFresh_AspisR72Sampler_Funs.field.QM31.mul = @AspisR72Sampler.field.QM31.mul := by
  funext l r
  delta AspisR72Sampler.PRVFresh_AspisR72Sampler_Funs.field.QM31.mul AspisR72Sampler.field.QM31.mul
  simp only [PRVEq.AspisR72Sampler.Funs.field.CM31.add, PRVEq.AspisR72Sampler.Funs.field.CM31.sub,
    PRVEq.AspisR72Sampler.Funs.field.CM31.mul, PRVEq.AspisR72Sampler.Funs.field.mul_by_r]
  by_cases hc : (l.c0.a.val < 2147483647 ∧ l.c0.b.val < 2147483647 ∧ l.c1.a.val < 2147483647 ∧ l.c1.b.val < 2147483647 ∧
      r.c0.a.val < 2147483647 ∧ r.c0.b.val < 2147483647 ∧ r.c1.a.val < 2147483647 ∧ r.c1.b.val < 2147483647)
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hc
    obtain ⟨res, hres, hch⟩ := AspisR72Sampler.PCVB_R72.qm31_mul_gate_eq_fresh l r h1 h2 h3 h4 h5 h6 h7 h8
    rw [hres]
    simp only [bind_tc_ok]
    exact hch
  · rw [AspisR72Sampler.PCVB_R72.r24_none l r hc]
    simp only [bind_tc_ok]
#print axioms PRVEq.AspisR72Sampler.Funs.field.QM31.mul
