import R1Z.PDict_WorkRounds222
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Static222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap

theorem semantic_sumcheck (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base)
    (hw : @PDict_WorkTransport222.WorkExtensional base ops)
    {H : Type} (digest : aspis_core.digest.Digest32 H)
    (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec U8)
    (initial : aspis_core.field.QM31) (x : @host_semantic.SemanticOracle base) :
    @host_sumcheck.prove_sumcheck (types base F) (selected base F ops) H _ digest
      (@host_semantic.SemanticOracle.Insts.Aspis_r1_cost_probeHost_sumcheckOracle (types base F) (selected base F ops))
      transcript output initial (oracle base F x) =
    @host_sumcheck.prove_sumcheck base ops H _ digest
      (@host_semantic.SemanticOracle.Insts.Aspis_r1_cost_probeHost_sumcheckOracle base ops)
      transcript output initial x := by
  rw [erase_238]
  apply PDict_WorkTransport222.sumcheck_transport ops hw
  intro point
  exact erase_161 base F ops x point

#print axioms semantic_sumcheck
end R1Z.PDict_Static222
