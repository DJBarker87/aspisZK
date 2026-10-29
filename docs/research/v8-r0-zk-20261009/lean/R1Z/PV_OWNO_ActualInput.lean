import R1Z.PV_OWNO_Builder
import R1Z.PV_OWNO_PointStores
import R1Z.PV_OWNM_V239
set_option autoImplicit false
namespace R1Z.PV_OWNO_ActualInput
open Aeneas Aeneas.Std PV_OWNK_TowerCanon PV_OWNO_HelperArrays

/-- The consuming Input uses the same successful column vector and reached
point state. This is a carrier map, not a replacement definition of native. -/
def input (pub : PV_OWNM_V239.Public) (site : PV_OWNM_V239.Site)
 (combine : U64 → U32 → U64) (writes : List PV_OWNO_PointStores.Write)
 (columns : List (List Q)) : PV_OWNM_V239.Input :=
 ⟨pub,site,PV_OWNO_PointStores.run combine writes,columns⟩

theorem canon_transport (q : Q) (h : Canon q) : PV_OWNM_V239.Canon q :=
 ⟨h.1.1,h.1.2,h.2.1,h.2.2⟩

/-- ActualInput for the source-stage model, with complete error-preserving
builder execution as its premise. Native source/carrier association must be
checked separately before this can be installed at the deployed consumer. -/
theorem of_builder_execution {E : Type} (publicError imbalance : E)
 (inverse : Q → Option Q) (base : Aeneas.Std.Array (List U32) 26#usize)
 (d g : Aeneas.Std.Array Q 1024#usize)
 (setup : Unit → Except E (Q × Q)) (registry : Q → Except E (List CopyRow))
 (balanced : List Q → Bool) (finish : List Q → Except E Unit) (columns : List (List Q))
 (built : PV_OWNO_Builder.build publicError imbalance inverse base d g setup registry balanced finish = .ok columns)
 (pub : PV_OWNM_V239.Public) (site : PV_OWNM_V239.Site)
 (combine : U64 → U32 → U64) (writes : List PV_OWNO_PointStores.Write) :
 PV_OWNM_V239.PV_OWNM_Link_ActualInput PV_OWNJ_Points.statement_points
  (input pub site combine writes columns) := by
 have hc := PV_OWNO_Builder.successful_canonical publicError imbalance inverse base d g
  setup registry balanced finish columns built
 have hp := PV_OWNO_PointStores.run_canonical combine writes
 have hl := PV_OWNO_PointStores.run_length combine writes
 refine ⟨hl,?_,?_⟩
 · intro p hmem
   refine ⟨(PV_OWNJ_Points.point_lengths _ p hmem).trans hl,?_⟩
   intro q hq
   exact canon_transport q (PV_OWNL_Inputs.statement_points_canon _ hp p hmem q hq)
 · intro c hmem q hq
   exact canon_transport q (hc c hmem q hq)

#print axioms canon_transport
#print axioms of_builder_execution
end R1Z.PV_OWNO_ActualInput
