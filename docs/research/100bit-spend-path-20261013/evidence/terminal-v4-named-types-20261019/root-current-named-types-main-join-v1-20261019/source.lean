import AspisR1PublicPreparation.Types
import AspisR1SelectedMaskProbe.Types

/-! Focused joint-owner check. Namespaced generated discriminant instances
permit the actual preparation and current terminal type owners to coexist.
This is not a replay of terminal functions or their dependent proofs. -/
open Aeneas Aeneas.Std
namespace AspisR1SelectedMaskProbe.NamedTypesMainJoin

theorem error_instance_reader
    (e : state_only_prefix.r0.Error) :
    Discriminant.read_discriminant e =
      state_only_prefix.r0.Error.read_discriminant e := rfl

theorem public_instance_reader
    (p : pool_v1.pair_forest_semantic_terminal.r0.Public) :
    Discriminant.read_discriminant p =
      pool_v1.pair_forest_semantic_terminal.r0.Public.read_discriminant p := rfl

theorem variant_instance_reader
    (v : pool_v1.pair_forest_semantic_terminal.CompiledVariant) :
    Discriminant.read_discriminant v =
      pool_v1.pair_forest_semantic_terminal.CompiledVariant.read_discriminant v := rfl

#print axioms error_instance_reader
#print axioms public_instance_reader
#print axioms variant_instance_reader
end AspisR1SelectedMaskProbe.NamedTypesMainJoin
