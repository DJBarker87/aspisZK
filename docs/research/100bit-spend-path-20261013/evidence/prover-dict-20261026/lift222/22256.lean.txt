import R1Z.PDict_PublicLeaves222
import Mathlib.Tactic.CasesM
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Static222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap
/-- Pointwise structural transport for `host_semantic.build_with_material.closure.Insts.CoreOpsFunctionFnOncePairQM31QM31ResultVecQM31Error.call_once`. -/
theorem erase_250 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) (h12 : PDict_MapErrTransport222.MapErrLaw base ops) :
    letI : ExternalTypes := base
    ∀ {H : Type} {T1 : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (CommitmentsInst : host_semantic.Commitments
  T1) (c : host_semantic.build_with_material.closure H T1) (tupled_args : (aspis_core.field.QM31 × aspis_core.field.QM31)),
    @host_semantic.build_with_material.closure.Insts.CoreOpsFunctionFnOncePairQM31QM31ResultVecQM31Error.call_once (types base F) (selected base F ops) H T1 aspis_coredigestDigest32Inst CommitmentsInst (compilation base F c.1, pub base F c.2) tupled_args =
    @host_semantic.build_with_material.closure.Insts.CoreOpsFunctionFnOncePairQM31QM31ResultVecQM31Error.call_once base ops H T1 aspis_coredigestDigest32Inst CommitmentsInst c tupled_args := by
  intro H T1 aspis_coredigestDigest32Inst CommitmentsInst c tupled_args
  rcases c with ⟨compiled, public1⟩
  delta host_semantic.build_with_material.closure.Insts.CoreOpsFunctionFnOncePairQM31QM31ResultVecQM31Error.call_once
  simp only [Aeneas.Std.uncurry, erase_249 base F ops h12,
    PDict_PublicLeaves222.transition, PDict_ResultTransport.bind_map]
  simp only [PDict_FormatterTypeMaps.compilation, PDict_FormatterTypeMaps.late,
    PDict_PublicLeaves222.helper]
  repeat first
    | rfl
    | (apply PDict_FallibleTransport.bind_congr; intro x;
        (try simp only [Aeneas.Std.uncurry, PDict_ResultTransport.bind_map,
          PDict_PublicLeaves222.transition, PDict_FormatterTypeMaps.late, PDict_PublicLeaves222.helper]))
    | (casesm* (_ × _), core.result.Result _ _, core.ops.control_flow.ControlFlow _ _, Bool <;>
        (try simp only [Aeneas.Std.uncurry, PDict_ResultTransport.bind_map,
          PDict_PublicLeaves222.transition, PDict_FormatterTypeMaps.late, PDict_PublicLeaves222.helper]))
#print axioms erase_250
end R1Z.PDict_Static222
