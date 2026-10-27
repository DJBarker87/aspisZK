import R1Z.PV_RunJoin_MapErrInstalled
import R1Z.PDict_MapErrTransport222
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_DictionaryIdentity
open ProverRwFull

theorem map_error (base : ExternalTypes)
    (ops : @ExternalFuns (PDict_CodecDictionary.native base)) :
    @PV_RunJoin_MapErrInstalled.Identity (PDict_CodecDictionary.native base)
      (PDict_CodecDictionary.selected base ops) :=
  PDict_MapErrTransport222.current_map_err base ops

theorem parametric (base : ExternalTypes)
    (ops : @ExternalFuns (PDict_CodecDictionary.native base)) :
    @PV_RunJoin_StoreContinuationResidual.MapErrParametric
      (PDict_CodecDictionary.native base) (PDict_CodecDictionary.selected base ops) :=
  @PV_RunJoin_MapErrInstalled.installed (PDict_CodecDictionary.native base)
    (PDict_CodecDictionary.selected base ops) (map_error base ops)

#print axioms map_error
#print axioms parametric
end R1Z.PV_RunJoin_DictionaryIdentity
