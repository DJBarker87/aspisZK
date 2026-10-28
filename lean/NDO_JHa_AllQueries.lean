import NDO_JHa_Query0
import NDO_JHa_Query1
import NDO_JHa_Query2
import NDO_JHa_Query3
import NDO_JHa_Query4
import NDO_JHa_Query5
import NDO_JHa_Query6
import NDO_JHa_Query7
import NDO_JHa_Query8
import NDO_JHa_Query9
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_AllQueries
open Aeneas Aeneas.Std Result AspisR1Stage2
open S7Kani3CallerTrace (PushTrace Sum)
open S7JoinRowsTrace (Progress)
abbrev ops := JGc_TX2_QueryDictionary.ops JGp_Seeds.query

theorem source (i : Fin 10) (p : verifier.Prepared) (a : verifier.Accumulator) (b : verifier.BatchedWeights)
    (old : S8OwnedP6Finish.Weights) (sum : Sum)
    (queries : p.queries=JFq_Queries.value) (alpha : p.alpha=JFo_Prepared.value.alpha)
    (next : a.next=JGw_GeometryReads.cursor i) (size : a.weights.val.length=64)
    (crhs : Port4C_QueryArithmetic.CanonE a.rhs)
    (cpower : Port3_FlushInstall.Canonical a.power)
    (crho : Port3_FlushInstall.Canonical p.rho)
    (history : PushTrace old (Port3_RowsInstall.toBW b) sum)
    (phase : Progress i.val 0 (Port3_RowsInstall.toBW b)) :
    ∃ out after sumOut,
      Port3_NativeQueryBody.verifier.candidate.query_values ops JFx_NativeBytes.proof p a JFr_TX2_Powers.value none
        (JGp_Geometry.value () JGp_Seeds.geometry) b=ok (.Ok (out,after)) ∧
      out.weights=a.weights ∧ out.next.val=i.val+1 ∧
      Port4C_QueryArithmetic.CanonE out.rhs ∧ Port3_FlushInstall.Canonical out.power ∧
      PushTrace old (Port3_RowsInstall.toBW after) sumOut ∧ Progress (i.val+1) 0 (Port3_RowsInstall.toBW after) := by
  fin_cases i
  · exact JHa_Query0.source p a b old sum queries alpha next size crhs cpower crho history phase
  · exact JHa_Query1.source p a b old sum queries alpha next size crhs cpower crho history phase
  · exact JHa_Query2.source p a b old sum queries alpha next size crhs cpower crho history phase
  · exact JHa_Query3.source p a b old sum queries alpha next size crhs cpower crho history phase
  · exact JHa_Query4.source p a b old sum queries alpha next size crhs cpower crho history phase
  · exact JHa_Query5.source p a b old sum queries alpha next size crhs cpower crho history phase
  · exact JHa_Query6.source p a b old sum queries alpha next size crhs cpower crho history phase
  · exact JHa_Query7.source p a b old sum queries alpha next size crhs cpower crho history phase
  · exact JHa_Query8.source p a b old sum queries alpha next size crhs cpower crho history phase
  · exact JHa_Query9.source p a b old sum queries alpha next size crhs cpower crho history phase
#print axioms source
end AspisR1.JHa_AllQueries
end
