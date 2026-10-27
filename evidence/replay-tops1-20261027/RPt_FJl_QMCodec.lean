import RPt_FJl_QMParser
import RPt_FJf_EbyKCodec
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_QMCodec
open Aeneas Aeneas.Std AspisR1CurrentWide.Proof
open ExactLeafFieldCodec RetainedFieldByteCodec RetainedExactLimbCodec
open FIo_FieldBridge (NQ qm)
def candidate (q : AspisR1CandidateParser.field.QM31) : QM31Exact :=
  ⟨⟨(q.c0.a.val : M31Exact),(q.c0.b.val : M31Exact)⟩,
    ⟨(q.c1.a.val : M31Exact),(q.c1.b.val : M31Exact)⟩⟩
theorem decoded (q : NQ) : candidate (FJl_QMParser.toCandidate q)=decodeQM (qm q) := rfl

theorem residue (v : M31Value) : m31ResidueEquiv v=(v.val : M31Exact) := by
  apply ZMod.val_injective
  change v.val=(v.val : M31Exact).val
  rw [ZMod.val_natCast_of_lt v.isLt]

theorem limbs (ls : QM31Limbs) :
    candidate (CandidateStrictQM31Parser.limbsToCandidate ls)=qm31ExactLimbEquiv ls := by
  apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;>
    simp only [candidate,CandidateStrictQM31Parser.limbsToCandidate,
      M31ParserRefinement.valueToU32_val,qm31ExactLimbEquiv,Equiv.coe_fn_mk,limbsToQM31Exact,residue]
#print axioms decoded
#print axioms residue
#print axioms limbs
end AspisR1.FJl_QMCodec
end
