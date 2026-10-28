import NDO_JHa_AllQueries
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_LineRead
open Aeneas Aeneas.Std Result AspisR1Stage2
attribute [local irreducible] JFx_NativeBytes.proof

def index (i : Fin 10) : Fin 22 := ⟨i.val,by omega⟩
def values (i : Fin 10) : Array SAQ_WideABI.E 4#usize := match i.val with
  | 0 => JGw_Values0.value | 1 => JGw_Values1.value
  | 2 => JGw_Values2.value | 3 => JGw_Values3.value
  | 4 => JGw_Values4.value | 5 => JGw_Values5.value
  | 6 => JGw_Values6.value | 7 => JGw_Values7.value
  | 8 => JGw_Values8.value | _ => JGw_Values9.value
def value (i : Fin 10) : SAQ_WideABI.E :=
  let inverse := JGw_Inverses.inverse () JGp_Seeds.geometry i
  match i.val with
  | 0 => JGw_Line0.value inverse | 1 => JGw_Line1.value inverse
  | 2 => JGw_Line2.value inverse | 3 => JGw_Line3.value inverse
  | 4 => JGw_Line4.value inverse | 5 => JGw_Line5.value inverse
  | 6 => JGw_Line6.value inverse | 7 => JGw_Line7.value inverse
  | 8 => JGw_Line8.value inverse | _ => JGw_Line9.value inverse

theorem values_call (seed : Port3_NativeQueryBody.Ops) (i : Fin 10) :
    (JGc_TX2_QueryDictionary.ops seed).op0 4#usize
      (Port3_NativeQueryBody.verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
        (JGc_TX2_QueryDictionary.ops seed))
      (JFo_Opening.value (index i))=ok (values i) := by
  fin_cases i
  · exact JGw_Values0.source (JGc_TX2_QueryDictionary.input seed)
  · exact JGw_Values1.source (JGc_TX2_QueryDictionary.input seed)
  · exact JGw_Values2.source (JGc_TX2_QueryDictionary.input seed)
  · exact JGw_Values3.source (JGc_TX2_QueryDictionary.input seed)
  · exact JGw_Values4.source (JGc_TX2_QueryDictionary.input seed)
  · exact JGw_Values5.source (JGc_TX2_QueryDictionary.input seed)
  · exact JGw_Values6.source (JGc_TX2_QueryDictionary.input seed)
  · exact JGw_Values7.source (JGc_TX2_QueryDictionary.input seed)
  · exact JGw_Values8.source (JGc_TX2_QueryDictionary.input seed)
  · exact JGw_Values9.source (JGc_TX2_QueryDictionary.input seed)
#print axioms values_call

theorem line_call (i : Fin 10) :
    SAQ_LineQuery.line JFq_Alpha1.scalar (values i)
      (JGw_Inverses.inverse () JGp_Seeds.geometry i)=ok (value i) := by
  fin_cases i
  · exact JGw_Line0.returned _
  · exact JGw_Line1.returned _
  · exact JGw_Line2.returned _
  · exact JGw_Line3.returned _
  · exact JGw_Line4.returned _
  · exact JGw_Line5.returned _
  · exact JGw_Line6.returned _
  · exact JGw_Line7.returned _
  · exact JGw_Line8.returned _
  · exact JGw_Line9.returned _
#print axioms line_call

theorem canonical (i : Fin 10) : Port4C_QueryArithmetic.CanonE (value i) := by
  fin_cases i
  · exact (Classical.choose_spec (JGw_Line0.source _)).2
  · exact (Classical.choose_spec (JGw_Line1.source _)).2
  · exact (Classical.choose_spec (JGw_Line2.source _)).2
  · exact (Classical.choose_spec (JGw_Line3.source _)).2
  · exact (Classical.choose_spec (JGw_Line4.source _)).2
  · exact (Classical.choose_spec (JGw_Line5.source _)).2
  · exact (Classical.choose_spec (JGw_Line6.source _)).2
  · exact (Classical.choose_spec (JGw_Line7.source _)).2
  · exact (Classical.choose_spec (JGw_Line8.source _)).2
  · exact (Classical.choose_spec (JGw_Line9.source _)).2
#print axioms canonical

/-- Recover the actual line operand from the SAME query's observations. -/
theorem source (i : Fin 10) (p : verifier.Prepared) (a out : verifier.Accumulator)
    (b after : verifier.BatchedWeights)
    (alpha : p.alpha=JFo_Prepared.value.alpha)
    (next : a.next=JGw_GeometryReads.cursor i)
    (run : Port3_NativeQueryBody.verifier.candidate.query_values JHa_AllQueries.ops
      JFx_NativeBytes.proof p a JFr_TX2_Powers.value none
      (JGp_Geometry.value () JGp_Seeds.geometry) b=ok (.Ok (out,after))) :
    ∃ o : Port4C_QueryValues.Observation JHa_AllQueries.ops JFx_NativeBytes.proof p a out
      JFr_TX2_Powers.value none (JGp_Geometry.value () JGp_Seeds.geometry) b after,
      o.value=value i ∧ Port4C_QueryArithmetic.CanonE o.value := by
  obtain ⟨o⟩ := Port4C_QueryValues.observed _ _ _ _ _ _ _ _ _ _ run
  have fields := JGc_TX2_QueryDictionary.fields JGp_Seeds.query
  have cursor : JGw_GeometryReads.cursor i=JFo_Opening.cursor (index i) := by
    apply UScalar.eq_of_val_eq
    rfl
  have opening := o.opening_read
  rw [fields.1,next,cursor] at opening
  have sameOpening := Result.ok.inj (opening.symm.trans (JFo_Opening.call (index i)))
  have read := o.values_read
  rw [sameOpening] at read
  have sameValues := Result.ok.inj (read.symm.trans (values_call JGp_Seeds.query i))
  have inverse := o.inverse_read
  rw [fields.2.1,next] at inverse
  have sameInverse := Result.ok.inj (inverse.symm.trans (JGw_Inverses.read () JGp_Seeds.geometry i))
  have ar := o.alpha1_read
  rw [alpha] at ar
  have selected : Array.index_usize JFo_Prepared.value.alpha 1#usize=ok JFq_Alpha1.scalar := rfl
  have sameAlpha := Result.ok.inj (ar.symm.trans selected)
  have line := o.line
  rw [fields.2.2.2.2.1,sameAlpha,sameValues,sameInverse] at line
  have same := Result.ok.inj (line.symm.trans (line_call i))
  exact ⟨o,same,by rw [same];exact canonical i⟩
#print axioms source
end AspisR1.JHk_LineRead
end
