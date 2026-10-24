import S6CurrentStage1FirstJoinV1
import S2Y_ForestPublic
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisS6CurrentNamedForestPort
open AspisR1.S2Y_ForestPublic AspisS6CurrentFirstInstallation

/-- Concrete full codec law at the exact named lead interface, including the
current first child. Other operations and native SDK effects remain separate. -/
theorem fullForestAcceptedRoundtrip (ops : AdapterRw.Ops) (vops : AspisR1CurrentCaller.Ops) :
    FullForestAcceptedRoundtrip (install ops vops) := by
  intro original statement encoded decoded encoded_actual
  exact AspisS6CurrentCodecInstallation.installed_roundtrip
    {ops with op10:=current vops} original statement encoded decoded encoded_actual

/-- The original lead consumer now requires no separate full codec law.
Identity of the reconstructed statement and child-input retention are retained
exactly; no SDK or cross-transaction identity is inferred from codec equality. -/
theorem reconstructed_bytes (ops : AdapterRw.Ops) (vops : AspisR1CurrentCaller.Ops)
    (original : Slice U8) (decoded reconstructed : Statement)
    (encoded : Array U8 1880#usize)
    (decode : (install ops vops).op47 original=ok (.Ok decoded))
    (encode : (install ops vops).op22 reconstructed=ok (.Ok encoded))
    (identity : reconstructed=decoded) :
    AspisR1.S2LeadInterface.bytesOf (Array.to_slice encoded).val =
      AspisR1.S2LeadInterface.bytesOf original.val ∧
    (AspisR1.S2LeadInterface.bytesOf original.val).length=1880 := by
  exact AspisR1.S2Y_ForestPublic.reconstructed_bytes (install ops vops)
    (fullForestAcceptedRoundtrip ops vops) original decoded reconstructed encoded decode encode identity

#print axioms fullForestAcceptedRoundtrip
#print axioms reconstructed_bytes
end AspisS6CurrentNamedForestPort
