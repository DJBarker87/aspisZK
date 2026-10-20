import WireBindingRecordCodec
import WireTx2ResumeCalls
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1Stage2.QvStage2Retained
open WireTx2

/-- Three ordered dictionary-equation witnesses from the complete retained
resume body. This does not assert completeness of an execution-effect log. -/
theorem resume_three_witnesses (ops : ResumeOps) {H : Type}
    (D : aspis_core.digest.Digest32 H)
    (bytes proof public1 : Slice U8) (v : transport.Variant) (hash : H)
    (p : verifier.Prepared) (acc : verifier.Accumulator)
    (success : verifier.resumeWithOps ops D bytes proof public1 v hash = ok (.Ok (p,acc))) :
    ∃ (body : Slice U8) (calls : List (Slice (Slice U8) × Array U8 32#usize)),
      calls.length = 3 ∧
      calls.map Prod.fst = [singletonParts proof, singletonParts public1, checksumParts body] ∧
      ∀ c ∈ calls, D.digest hash c.1 = ok c.2 := by
  obtain ⟨_, body, d0, d1, d2, _, _, h0, h1, h2⟩ :=
    resume_three_inputs ops D bytes proof public1 v hash p acc success
  refine ⟨body, [(singletonParts proof,d0), (singletonParts public1,d1),
    (checksumParts body,d2)], rfl, rfl, ?_⟩
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2

#print axioms resume_three_witnesses
end AspisR1Stage2.QvStage2Retained
