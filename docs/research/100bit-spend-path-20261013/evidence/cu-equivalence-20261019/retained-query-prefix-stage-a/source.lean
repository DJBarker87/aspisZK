import CuSavingsRetainedQueryPrefixLoop
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedQueryPrefixStage
open Aeneas Aeneas.Std Result
open CuSavingsRetainedQueryPrefixBinding CuSavingsRetainedQueryPrefixLoop
variable [AspisR1CanonicalDots.Shared] [AspisR1CanonicalSampler.Shared]
  [AspisR1CanonicalReader.Runtime] [AspisR1CanonicalKReader.Runtime] [AspisR1CuRho.ScalarKBlocks]
  [AspisR1RhoAccumulate.AccumulateCommon] [AspisR1CuRho.HeapReserve]

theorem body_eq (common : AspisR1RhoQuery.QueryCommon) (B : Boundaries)
    (dot : AspisR1RetainedDots.Shared) {H : Type} (D : Q.D H) (v : Q.View)
    (v1 : AspisR1RhoQuery.transport.Variant) (we : Q.E) (o : Option (Array U8 32#usize))
    (p : Q.Prepared) (g : G) (hg : SourceTable g)
    (hash : H) (obs : Option (Q.Phase→Result Unit)) (geometry : Q.Geometry) (end1 : Usize)
    (a : AspisR1RhoQuery.verifier.Accumulator) (pending : AspisR1RhoQuery.BatchedWeights) :
    (letI : AspisR1RhoQuery.QueryCommon:=newBinding common B dot
     AspisR1RhoStage.stage_new_loop.body D v v1 we o p g hash obs geometry end1 a pending) =
    (letI : AspisR1RhoQuery.QueryCommon:=oldBinding common B dot
     AspisR1RhoStage.stage_new_loop.body D v v1 we o p g hash obs geometry end1 a pending) := by
  unfold AspisR1RhoStage.stage_new_loop.body
  rw [stage_query_new_eq common B dot D {v with variant:=v1,inactive:=we,folded_root:=o}
    p a g hg hash obs geometry pending]

theorem loop_eq (common : AspisR1RhoQuery.QueryCommon) (B : Boundaries)
    (dot : AspisR1RetainedDots.Shared) {H : Type} (D : Q.D H) (v : Q.View)
    (v1 : AspisR1RhoQuery.transport.Variant) (we : Q.E) (o : Option (Array U8 32#usize))
    (p : Q.Prepared) (a : AspisR1RhoQuery.verifier.Accumulator) (g : G) (hg : SourceTable g)
    (hash : H) (obs : Option (Q.Phase→Result Unit)) (geometry : Q.Geometry) (end1 : Usize)
    (pending : AspisR1RhoQuery.BatchedWeights) :
    (letI : AspisR1RhoQuery.QueryCommon:=newBinding common B dot
     AspisR1RhoStage.stage_new_loop D v v1 we o p a g hash obs geometry end1 pending) =
    (letI : AspisR1RhoQuery.QueryCommon:=oldBinding common B dot
     AspisR1RhoStage.stage_new_loop D v v1 we o p a g hash obs geometry end1 pending) := by
  unfold AspisR1RhoStage.stage_new_loop
  have hbody :
      (fun s=>letI : AspisR1RhoQuery.QueryCommon:=newBinding common B dot
        AspisR1RhoStage.stage_new_loop.body D v v1 we o p g hash obs geometry end1 s.1 s.2) =
      (fun s=>letI : AspisR1RhoQuery.QueryCommon:=oldBinding common B dot
        AspisR1RhoStage.stage_new_loop.body D v v1 we o p g hash obs geometry end1 s.1 s.2) := by
    funext s
    exact body_eq common B dot D v v1 we o p g hg hash obs geometry end1 s.1 s.2
  rw [hbody]

theorem stage_eq (common : AspisR1RhoQuery.QueryCommon) (B : Boundaries)
    (dot : AspisR1RetainedDots.Shared) {H : Type} (D : Q.D H) (v : Q.View)
    (p : Q.Prepared) (a : AspisR1RhoQuery.verifier.Accumulator) (g : G) (hg : SourceTable g)
    (hash : H) (obs : Option (Q.Phase→Result Unit)) (geometry : Q.Geometry) (end1 : Usize) :
    (letI : AspisR1RhoQuery.QueryCommon:=newBinding common B dot
     AspisR1RhoStage.stage_new D v p a g hash obs geometry end1) =
    (letI : AspisR1RhoQuery.QueryCommon:=oldBinding common B dot
     AspisR1RhoStage.stage_new D v p a g hash obs geometry end1) := by
  unfold AspisR1RhoStage.stage_new
  simp only [loop_eq common B dot D v v.variant v.inactive v.folded_root p a g hg hash obs geometry end1]

#print axioms body_eq
#print axioms loop_eq
#print axioms stage_eq
end AspisR1.CuSavingsRetainedQueryPrefixStage
