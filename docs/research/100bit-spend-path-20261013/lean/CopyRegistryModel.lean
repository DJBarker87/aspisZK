import AspisR1.CopyRegistryBounds

/-! The retained mathematical registry is exactly the same 136 source
records. This is equality of small literal descriptors, without field arithmetic. -/
set_option autoImplicit false
namespace AspisR1.CopyRegistryModel
open AspisR1.CopyLinkWeightExact AspisR1.CopyRegistryBounds

def modelRegistry : List R0P.CopyLink :=
  registry.val.attach.map fun entry =>
    modelLink entry.val (member_bounds entry.val entry.property).2.1
      (member_bounds entry.val entry.property).2.2.2

theorem modelRegistry_length : modelRegistry.length = 136 := by
  change (registry.val.attach.map _).length = 136
  rw [List.length_map, List.length_attach, registry.property]
  rfl

def rawAt (i : Fin 136) : Raw :=
  registry.val[i.val]'(by simpa [registry.property] using i.isLt)

def modelAt (i : Fin 136) : R0P.CopyLink :=
  modelLink (rawAt i)
    (member_bounds (rawAt i) (List.getElem_mem _)).2.1
    (member_bounds (rawAt i) (List.getElem_mem _)).2.2.2

theorem modelRegistry_getElem (i : Fin 136) :
    modelRegistry[i.val]'(by rw [modelRegistry_length]; exact i.isLt) = modelAt i := by
  simp only [modelRegistry, List.getElem_map, List.getElem_attach]
  rfl

/-- No free model registry: both endpoints and all weight/tag fields agree
record for record with the fixed retained Copy model. -/
theorem model_registry_exact : modelRegistry = R0P.copyLinks := by
  unfold modelRegistry registry AspisR1CopyLinkLoopCandidate.pool_v1.pair_forest_copy_terminal.constants.COPY_LINKS
  rfl

#print axioms modelRegistry_length
#print axioms modelRegistry_getElem
#print axioms model_registry_exact
end AspisR1.CopyRegistryModel
