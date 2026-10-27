import R1Z.PDict_LateNe222
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Static222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap

theorem erase_257 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base)
    (hw : @PDict_WorkTransport222.WorkExtensional base ops)
    (h12 : PDict_MapErrTransport222.MapErrLaw base ops) :
    letI : ExternalTypes := base
    ∀ {H T : Type} (digest : aspis_core.digest.Digest32 H) (ci : host_semantic.Commitments T)
    (public1 : Public) (compiled : Compilation)
    (noised : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
    (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
    (d g padding : Array aspis_core.field.QM31 1024#usize)
    (commitments : T) (hash : H) (variant : transport.Variant),
    @host_semantic.build_with_material (types base F) (selected base F ops) H T digest ci
      (pub base F public1) (compilation base F compiled) noised mask_only d g padding commitments hash variant =
    @host_semantic.build_with_material base ops H T digest ci
      public1 compiled noised mask_only d g padding commitments hash variant := by
  intro H T digest ci public1 compiled noised mask_only d g padding commitments hash variant
  have hm (c1 : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize) :
      @host_semantic.build_with_helper_mode (types base F) (selected base F ops) H _ T digest
        (@host_semantic.build_with_material.closure.Insts.CoreOpsFunctionFnOncePairQM31QM31ResultVecQM31Error
          (types base F) (selected base F ops) H T digest ci) ci
        (pub base F public1) c1 d g padding (compilation base F compiled, pub base F public1) commitments hash variant =
      @host_semantic.build_with_helper_mode base ops H _ T digest
        (@host_semantic.build_with_material.closure.Insts.CoreOpsFunctionFnOncePairQM31QM31ResultVecQM31Error
          base ops H T digest ci) ci
        public1 c1 d g padding (compiled, public1) commitments hash variant := by
    apply erase_241 base F ops hw
    intro l c
    exact @erase_250 base F ops h12 H T digest ci (compiled, public1) (l,c)
  simp only [PDict_FormatterTypeMaps.compilation] at hm
  delta host_semantic.build_with_material
  simp only [PDict_FormatterTypeMaps.compilation, PDict_PublicLeaves222.transition,
    PDict_ResultTransport.bind_map, late_ne, erase_256, hm]
  all_goals rfl

#print axioms erase_257
end R1Z.PDict_Static222
