import NDO_JFw_Prefix
import NDO_PSem_ExpansionUnique
set_option autoImplicit false
namespace AspisR1.JFw_ArbitraryInitial
open Aeneas Aeneas.Std Result
open AspisS1NativeCompact AspisS1ValuesOwnedInstallation

theorem accepted (initial : Slice U8) (length : initial.length = 13831) :
    ∃ (expanded : Slice U8) (pre : AspisR1PublicPreparation.r1_wire.Prefix),
      compact.expand_semantic nativeValues JFw_RealExpansion.stored initial = ok (.Ok (),expanded) ∧
      AspisR1PublicPreparation.PrefixAdapter.parseAccepted expanded = ok (.Ok pre) := by
  obtain ⟨original,pre,call,parse,_⟩ := JFw_Prefix.inhabited
  obtain ⟨expanded,expand⟩ := JFw_Entry.success JFw_RealExpansion.stored initial
    JFw_RealExpansion.stored_length length
  have same := PSem_ExpansionUnique.carrier_unique JFw_RealExpansion.stored
    initial JFw_RealExpansion.initial expanded original expand call
  exact ⟨expanded,pre,expand,by rw [same];exact parse⟩

#print axioms accepted
end AspisR1.JFw_ArbitraryInitial
