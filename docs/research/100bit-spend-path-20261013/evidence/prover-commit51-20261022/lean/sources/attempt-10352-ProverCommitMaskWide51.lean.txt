import R1Z.ProverCommitConcreteMask51
import R1Z.ProverCommitMaskMap51
import R1Z.ProverCommitClaimMap51
import R1Z.ProverCommitWideBasis51
/-! Complete native mask-read value on the retained WideExact payload carrier. -/
set_option autoImplicit false
namespace R1Z.ProverCommitMaskWide51
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
open R0P.SemSource
open ProverCommitWideBasis51 (embed)

attribute [local irreducible] ProverCommitNativeQ48.source ProverCommitQArray48.array

theorem exact_result (p : Nat → Old.Q) (hp : ∀ i, i<10 → Canonical (p i))
    (c : Nat → Nat → Old.Q) (hc : ∀ i, i<29 → ∀ j, j<1024 → Canonical (c i j))
    (t : R0P.Trace QM31Exact) (ht : ∀ l : Fin 29, ∀ j : Fin 1024, decode (c l.val j.val)=t l j) :
    ∃ z : Old.Q, ProverCommitMaskRead51.run (ProverCommitQArray48.array 10#usize p) (ProverCommitMaskColumns51.columns c)
      (ProverCommitQArray48.array 1024#usize (c 27))=ok (ProverCommitNativeQ48.source z) ∧
      Canonical z ∧ embed (decode z)=R0P.Mask.maskValue ProverCommitWideBasis51.basis
        (fun i : Fin 16 => honestClaims (fun l j => embed (t l j)) (fun j : Fin 10 => embed (decode (p j.val))) 0 (Fin.castLE (by omega) i))
        (fun i : Fin 10 => honestClaims (fun l j => embed (t l j)) (fun j : Fin 10 => embed (decode (p j.val))) 0 ⟨16+i.val,by omega⟩)
        (honestClaims (fun l j => embed (t l j)) (fun j : Fin 10 => embed (decode (p j.val))) 0 27)
        (fun i : Fin 10 => embed (decode (p i.val))) := by
  obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitConcreteMask51.exact_result p hp c hc t ht
  refine ⟨z,hz,hcz,?_⟩
  rw [hdz,ProverCommitMaskMap51.value embed ProverCommitQBasis51.basis ProverCommitWideBasis51.basis
    ProverCommitWideBasis51.basis_i ProverCommitWideBasis51.basis_u]
  simp only [ProverCommitClaimMap51.claims]

#print axioms exact_result
end R1Z.ProverCommitMaskWide51
