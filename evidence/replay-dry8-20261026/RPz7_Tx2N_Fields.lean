import RPz7_Tx2N_Reader
import Port5Q1_QueryPorts
set_option autoImplicit false
noncomputable section
namespace AspisR1.Tx2N_Fields
open Aeneas Aeneas.Std Result AspisR1Stage2
open OraclePortCheckpointAbiC5 OraclePortCheckpointResumeC5

theorem canonical_k (x : K) : Port3_FlushInstall.Canonical (CheckpointBytes4ReaderFields.sourceK x) := by
  unfold Port3_FlushInstall.Canonical CheckpointBytes4ReaderFields.sourceK
  simp only [CheckpointBytes3Namespaces.fromK,CheckpointBytes3KDecode.rawK,
    CheckpointBytes3KDecode.rawLimbs,CheckpointBytes3ScalarShape.kWords,
    M31ParserRefinement.valueToU32_val]
  exact ⟨(RetainedExactLimbCodec.qm31ExactLimbEquiv.symm x 0).isLt,
    (RetainedExactLimbCodec.qm31ExactLimbEquiv.symm x 1).isLt,
    (RetainedExactLimbCodec.qm31ExactLimbEquiv.symm x 2).isLt,
    (RetainedExactLimbCodec.qm31ExactLimbEquiv.symm x 3).isLt⟩

theorem canonical_e (x : E) : Port4C_QueryArithmetic.CanonE (CheckpointBytes4ReaderFields.sourceE x) :=
  ⟨canonical_k x.re,canonical_k x.im⟩

/-- Prepared provenance and resumed accumulator canonicality follow from
reader fields; none is a second model-state premise. -/
theorem prepare (p : verifier.Prepared) (a : verifier.Accumulator)
    (c : Context) (data : MatchingSupport.Data E) (rho : K) (q : Fin 22 → Fin 262144)
    (am : QueryAccumulator.State K E)
    (fields : CheckpointBytes4SavedFields.BodyMatches p a (prepared c data rho q) am) :
    Port5Q1_QueryPorts.SessionAPrepare p data q rho ∧
    a.weights.val.length = 64 ∧ Port3_FlushInstall.Canonical a.power ∧
    Port4C_QueryArithmetic.CanonE a.rhs := by
  refine ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_⟩
  · intro j hj
    have mapped := congrArg (fun xs : List Nat => xs[j]?) fields.queries
    simp only [prepared,List.getElem?_map,List.getElem?_ofFn,hj,↓reduceDIte] at mapped
    have room : j < p.queries.val.length := by rw [p.queries.property]; exact hj
    simpa only [Port5Q1_GeometryBinding.queryAt,List.getElem?_eq_getElem room,
      Option.map_some,Option.getD_some,Option.some.injEq] using mapped
  · rw [fields.rho,CheckpointBytes5Output.ofK_source]; rfl
  · rw [fields.rho]; exact canonical_k rho
  · intro alpha read
    have at1 : Array.index_usize p.alpha 1#usize = ok (CheckpointBytes4ReaderFields.sourceE data.alpha1) := by
      simp [Array.index_usize,fields.alpha,prepared]
    have equal := Result.ok.inj (read.symm.trans at1)
    rw [equal,CheckpointBytes5Output.ofE_source]
  · rw [fields.weights,List.length_map,List.length_ofFn]
  · rw [fields.power]; exact canonical_k _
  · rw [fields.rhs]; exact canonical_e _

#print axioms canonical_k
#print axioms canonical_e
#print axioms prepare
end AspisR1.Tx2N_Fields
end
