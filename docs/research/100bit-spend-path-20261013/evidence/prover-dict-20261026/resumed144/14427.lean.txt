import R1Z.PDict_FileFlush
import R1Z.PDict_ClientFormatterIndependent
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Stage3Dictionary
open Aeneas Aeneas.Std ProverRwFull
abbrev native := PDict_FileFlush.native
abbrev selected := PDict_FileFlush.selected

/-- The actual extracted proof-account caller needs no op85 law under this
simultaneous dictionary. File/IO world, entropy/ROM and RunJoin stay explicit. -/
theorem client_without_debug (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @RealR1_client.prove_for_proof_accounts (native base)
      (@PDict_FormatterIndependent.erased (native base) (selected base ops)) =
    @RealR1_client.prove_for_proof_accounts (native base) (selected base ops) :=
  @PDict_ClientFormatterIndependent.client_erased (native base) (selected base ops)

#print axioms client_without_debug
end R1Z.PDict_Stage3Dictionary
