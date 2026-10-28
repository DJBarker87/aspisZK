import RPz7_F3L_OrdinaryMeaning
import NDO_JFw_TX2_ValueUnique
import NDO_JHa_Powers
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_OrdinaryValue
open Aeneas Aeneas.Std Result AspisR1ClaimPreparedBridge
open AspisR1CurrentCaller.InstalledPreparation

def toNative (x : PE) : FIo_Install.NE := FIo_Install.toE (Tx1Q_Carriers.e (currentE x))
def fromNative (x : FIo_Install.NE) : PE :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
    ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩

theorem identify (block : Array U8 32#usize) (target : FIo_Install.NE)
    (canon : FIo_WideValues.Canon target)
    (value : AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide target)=
      R0C.ModuloField.ordinary (AspisV8R19.SqueezeOracleBridge.decodeState block))
    (out : PE) (sample : AspisR1Post25SamplerOrdinaryCallbackV2.candidateOrdinaryPublic block=ok out) :
    out=fromNative target := by
  have canonical := AspisR1Post25SamplerOrdinaryCallbackV2.candidateOrdinaryPublic_success_canonical block out sample
  have meaning := F3L_OrdinaryMeaning.value block out sample
  have cn : FIo_WideValues.Canon (toNative out) := canonical
  have eq : toNative out=target := JFw_TX2_ValueUnique.native _ _ cn canon (meaning.trans value.symm)
  have back := congrArg fromNative eq
  exact back
#print axioms identify
end AspisR1.JHa_OrdinaryValue
end
