import R1Z.ProverCommitEncoderGeometry54
import R1Z.ProverCommitEncoderNodes54
import R1Z.ProverCommitEncoderMath54
/-! Lifting the proven base-field node values into the actual WideExact
recurrence. Embeddings preserve every repeated-doubling factor. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitEncoderLift54
open Aeneas Aeneas.Std Result
open ProverCommitWideOps48 ProverCommitEncoderEval54
open AspisCircleTensorBinding AspisCircleGroupOrder

theorem map_doubled {K L : Type} [CommRing K] [CommRing L] (f : K →+* L) (x : K) (n : Nat) :
    f (doubledFactor x n)=doubledFactor (f x) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [doubledFactor,map_sub,map_mul,map_ofNat,map_pow,map_one,ih]

theorem base_value (p : U32) :
    value (base p)=algebraMap (ZMod P) Exact (ProverCommitM31Ops48.decode p) := rfl

theorem nodes_image (j : Usize) (u : Fin 262144) (hj : j.val=u.val) :
    ∃ p : Nat → U32,
      AspisR1ProducerRelease47.nodes54.nodes j=ok (nodes p) ∧
      (∀ i, i<9 → (p i).val<2147483647) ∧
      ∀ i, i<9 → value (base (p i))=
        doubledFactor (algebraMap (ZMod P) Exact
          (AspisV7ExactOneFoldDomains.storedFirstLineX18 u)) i := by
  obtain ⟨p,hp,hcp,hdp⟩ := ProverCommitEncoderNodes54.exact_result j (by rw [hj];exact u.isLt)
  refine ⟨p,hp,hcp,?_⟩
  intro i hi
  rw [base_value,hdp i hi,hj,ProverCommitEncoderGeometry54.node_value u i (by omega),map_doubled]

#print axioms map_doubled
#print axioms base_value
#print axioms nodes_image
end R1Z.ProverCommitEncoderLift54
