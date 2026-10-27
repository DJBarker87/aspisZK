import R1Z.BuilderRecordCanonical

/-! Decoding canonical raw records recovers the complete semantic witness,
including all pair coordinates and direction bits. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_CanonicalDecode
open R0Z.WriterRefine R0Z.BuilderModel R1J.SpendWitnessMap

def fromModel (m : ModelWitness F) : AspisR1.SpendRelation.Wspend :=
  {inputValue := m.inputValue,outputValue := m.outputValue,changeValue := m.changeValue,
   sk := m.sk,salt := m.salt,path := m.path,
   pair := ⟨m.pairFirst,m.pairOccupied,m.pairSecond,m.pairInverse⟩,
   recipientOwner := m.recipientOwner,recipientSalt := m.recipientSalt,
   changeOwner := m.changeOwner,changeSalt := m.changeSalt}

theorem from_model (w : AspisR1.SpendRelation.Wspend) :
    fromModel (BuilderSpendRelation.modelWitness w) = w := by cases w; rfl

theorem map_self (w : ModelWitness F) : mapW (K := F) w = w := by
  simp only [mapW,ι_apply,ZMod.natCast_zmod_val] <;> rfl

theorem roundtrip (w : AspisR1.SpendRelation.Wspend) :
    BuilderRecordCanonical.witness (BuilderCanonical.rustWitness w) = w := by
  change fromModel (toModel (toRust (BuilderSpendRelation.modelWitness w))) = w
  rw [toModel_toRust,map_self,from_model]

#print axioms from_model
#print axioms map_self
#print axioms roundtrip
end R1Z.PV_Src_CanonicalDecode
