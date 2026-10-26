import Rc4_Install
import Rc4_Model
import SAQ_Nonvacuity
set_option autoImplicit false
noncomputable section
namespace AspisR1.Rc4_Nonvacuity

theorem contracts {F C : Type} (err : C) (c : DrvC_Installation.Configuration F C)
    (r : NP6_StdModel.Reservation) :
    Port5Q1_QueryPorts.SessionAPrimitives (Rc4_Install.configuration err c r).query ∧
    Port5Q1_GeometryCanonical.SessionAPrimitives (Rc4_Install.configuration err c r).geometry ∧
    Port5Q1_Domain.SessionADomain (Rc4_Install.configuration err c r).geometry :=
  ⟨SAQ_Decoder.primitives c.query,SAQ_Constructor.canonical err c.geometry,
    SAQ_Constructor.domain err c.geometry⟩

theorem model_surjective (i : F3_Model.Input) :
    ∃ raw : Rc4_Model.Input, Rc4_Model.typed raw=i :=
  ⟨Rc4_Model.erase i,Rc4_Model.typed_erase i⟩

theorem data_surjective (rs : LiteralAcceptanceTerminal.TranscriptRounds)
    (i : R1FinalSoundness.SourceInputs) (read : LiteralMatchingData.read rs=some i.data) :
    ∃ metadata : TxS_Carriers.Metadata, TxS_Carriers.source metadata rs=i :=
  ⟨TxS_Carriers.eraseInput i,TxS_Carriers.source_of_read rs i read⟩

#print axioms contracts
#print axioms model_surjective
#print axioms data_surjective
end AspisR1.Rc4_Nonvacuity
end
