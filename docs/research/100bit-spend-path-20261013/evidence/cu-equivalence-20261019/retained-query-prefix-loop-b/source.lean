import CuSavingsRetainedQueryPrefixBinding
import AspisR1RhoStage.Funs
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedQueryPrefixLoop
open Aeneas Aeneas.Std Result
open CuSavingsRetainedQueryPrefixBinding
variable [AspisR1CanonicalDots.Shared] [AspisR1CanonicalSampler.Shared]
  [AspisR1CanonicalReader.Runtime] [AspisR1CanonicalKReader.Runtime] [AspisR1CuRho.ScalarKBlocks]
  [AspisR1RhoAccumulate.AccumulateCommon] [AspisR1CuRho.HeapReserve]
attribute [local irreducible] sourcePrefix

theorem query_new_eq (common : AspisR1RhoQuery.QueryCommon) (B : Boundaries)
    (dot : AspisR1RetainedDots.Shared) {H : Type} (D : Q.D H) (v : Q.View)
    (p : Q.Prepared) (a : AspisR1RhoQuery.verifier.Accumulator) (g : G) (hg : SourceTable g)
    (hash : H) (obs : Option (Q.Phase→Result Unit)) (geometry : Q.Geometry)
    (pending : AspisR1RhoQuery.BatchedWeights) :
    (letI : AspisR1RhoQuery.QueryCommon:=newBinding common B dot
     AspisR1RhoQuery.query_new.query_with_geometry D v p a g hash obs geometry pending) =
    (letI : AspisR1RhoQuery.QueryCommon:=oldBinding common B dot
     AspisR1RhoQuery.query_new.query_with_geometry D v p a g hash obs geometry pending) := by
  dsimp only [newBinding,oldBinding]
  simp only [AspisR1RhoQuery.query_new.query_with_geometry,AspisR1RhoQuery.source_query_prefix]
  dsimp only
  rw [sourcePrefix_eq B dot D v p g hg hash obs geometry a.next]

theorem stage_query_new_eq (common : AspisR1RhoQuery.QueryCommon) (B : Boundaries)
    (dot : AspisR1RetainedDots.Shared) {H : Type} (D : Q.D H) (v : Q.View)
    (p : Q.Prepared) (a : AspisR1RhoQuery.verifier.Accumulator) (g : G) (hg : SourceTable g)
    (hash : H) (obs : Option (Q.Phase→Result Unit)) (geometry : Q.Geometry)
    (pending : AspisR1RhoQuery.BatchedWeights) :
    (letI : AspisR1RhoQuery.QueryCommon:=newBinding common B dot
     AspisR1RhoStage.stage_query_new D v p a g hash obs geometry pending) =
    (letI : AspisR1RhoQuery.QueryCommon:=oldBinding common B dot
     AspisR1RhoStage.stage_query_new D v p a g hash obs geometry pending) := by
  unfold AspisR1RhoStage.stage_query_new
  rw [query_new_eq common B dot D v p a g hg hash obs geometry pending]

#print axioms query_new_eq
#print axioms stage_query_new_eq
end AspisR1.CuSavingsRetainedQueryPrefixLoop
