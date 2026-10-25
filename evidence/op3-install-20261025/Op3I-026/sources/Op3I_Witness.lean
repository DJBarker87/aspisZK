import Op3I_Nonvacuity
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.Op3I_Witness

def prefix : List U8 :=
  [82#u8,49#u8,80#u8,51#u8,67#u8,66#u8,49#u8,56#u8,2#u8]

def proof : Slice U8 := ⟨prefix ++ List.replicate 57598 0#u8, by
  simp only [List.length_append,List.length_replicate,prefix,List.length_cons,List.length_nil]
  scalar_tac⟩

theorem fields : proof.val.length = 57607 ∧
    proof.val.take 8 = Op3I_Source.compact.MAGIC.val ∧
    proof.val[8]? = some 2#u8 ∧
    (proof.val.drop 9).take 7 = List.replicate 7 0#u8 := by
  have prefixLength : prefix.length = 9 := rfl
  refine ⟨?_,?_,?_,?_⟩
  · simp only [proof,List.length_append,prefixLength,List.length_replicate]
  · simp only [proof,List.take_append,prefixLength,show 8-9=0 by decide,
      List.take_zero,List.append_nil,Op3I_Source.compact.MAGIC]
    rfl
  · simp only [proof,List.getElem?_append,prefixLength,show 8<9 by decide,if_true]
    rfl
  · simp only [proof,List.drop_append,prefixLength,Nat.sub_self,List.drop_zero]
    have dropPrefix : prefix.drop 9 = [] := by rfl
    simp only [dropPrefix,List.nil_append,List.take_replicate,show min 7 57598=7 by decide]

theorem source_success : Op3I_Install.sourceBody proof = ok (.Ok .S2) :=
  Op3I_Nonvacuity.source_of_fields proof fields.1 fields.2.1 fields.2.2.1 fields.2.2.2

/-- This witness checks only shape acceptance, not a valid full proof/run. -/
theorem frozen_header_success :
    OraclePortHeader.accepts (MultiproofConeCanonical.bytesOf proof.val) = true :=
  (Op3I_Install.header_of_success proof .S2 source_success).2

#print axioms fields
#print axioms source_success
#print axioms frozen_header_success
end AspisR1.Op3I_Witness
end
