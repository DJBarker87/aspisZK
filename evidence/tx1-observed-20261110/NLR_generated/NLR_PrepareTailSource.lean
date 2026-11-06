import NLR_PrepareTails
import NLJ_RunAlgebra
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_PrepareTails
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code run)
/-- Full source equality, not a physical native association. -/
theorem tail_source (cfg : NLJ_Prepare.Configuration) {H : Type}
 (i : NLJ_Prepare.Input H) :
 run (tail_allocate cfg i) = run (SdkD_PrepareSource.code cfg.base cfg.boundaries cfg.std
  i.digest i.publicValue i.proof i.hash i.scratch) := by
 unfold tail_allocate tail_split tail_semanticRange tail_expandSemantic tail_valueRange
  tail_expandValues tail_rebuild tail_view tail_semantic tail_mapSemantic tail_mark tail_constructor
  SdkD_PrepareSource.code S1PrepareCode.prepare
 repeat' first
 | (solve | rfl)
 | (apply NLJ_RunAlgebra.bind_congr; intro)
 | split
#print axioms tail_source
#print tail_source
end AspisR1.NLR_PrepareTails
end
