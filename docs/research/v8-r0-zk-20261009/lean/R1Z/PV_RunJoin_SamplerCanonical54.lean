import R1Z.PV_RunJoin_SamplerDigits54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_SamplerCanonical54
open PV_RunJoin_CircleRawSampler52 PV_RunJoin_CircleNeutralShape53

theorem complete (block : Array U8 32#usize) :
    ∃ y, shipped_sampler.qm31_sample block=ok y ∧ QC y := by
  obtain ⟨digits,hd,hc⟩ := PV_RunJoin_SamplerDigits54.complete block
  let read (i : Fin 4) := digits.val[i.val]'(by rw [digits.property];exact i.isLt)
  have index (i : Fin 4) : Array.index_usize digits (Usize.ofNatCore i.val (by scalar_tac))=ok (read i) :=
    ProverCommitArrayIndex25.array_index_usize_ok _ _ i.isLt
  refine ⟨((read 0,read 1),(read 2,read 3)),?_,⟨⟨hc 0 (by decide),hc 1 (by decide)⟩,⟨hc 2 (by decide),hc 3 (by decide)⟩⟩⟩
  unfold shipped_sampler.qm31_sample
  rw [hd,bind_tc_ok]
  have h0 : Array.index_usize digits 0#usize=ok (read 0) := index 0
  have h1 : Array.index_usize digits 1#usize=ok (read 1) := index 1
  have h2 : Array.index_usize digits 2#usize=ok (read 2) := index 2
  have h3 : Array.index_usize digits 3#usize=ok (read 3) := index 3
  simp only [h0,h1,h2,h3,PV_RunJoin_CircleRawTower52.field.CM31.new,bind_tc_ok]
#print axioms complete
end R1Z.PV_RunJoin_SamplerCanonical54
