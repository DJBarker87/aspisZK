import NDO_JFr_Decode00
import NDO_JFr_Decode01
import NDO_JFr_Decode02
import NDO_JFr_Decode03
import NDO_JFr_Decode04
import NDO_JFr_Decode05
import NDO_JFr_Decode06
import NDO_JFr_Decode07
import NDO_JFr_Decode08
import NDO_JFr_Decode09
import NDO_JFr_RecordsAt
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFr_RealRounds
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1ExtractedRoundChildren AspisS1NativeCompact AspisS1ValuesOwnedInstallation
def polynomial (r : Fin 10) : Array MainQM 28#usize := match r.val with
  | 0 => JFr_Round00.polynomial
  | 1 => JFr_Round01.polynomial
  | 2 => JFr_Round02.polynomial
  | 3 => JFr_Round03.polynomial
  | 4 => JFr_Round04.polynomial
  | 5 => JFr_Round05.polynomial
  | 6 => JFr_Round06.polynomial
  | 7 => JFr_Round07.polynomial
  | 8 => JFr_Round08.polynomial
  | _ => JFr_Round09.polynomial
def challenges (r : Fin 10) : Array MainQM 10#usize := match r.val with
  | 0 => JFr_Round00.challenges
  | 1 => JFr_Round01.challenges
  | 2 => JFr_Round02.challenges
  | 3 => JFr_Round03.challenges
  | 4 => JFr_Round04.challenges
  | 5 => JFr_Round05.challenges
  | 6 => JFr_Round06.challenges
  | 7 => JFr_Round07.challenges
  | 8 => JFr_Round08.challenges
  | _ => JFr_Round09.challenges
def running (r : Fin 10) : MainQM := match r.val with
  | 0 => genToMain JFr_Data00.running
  | 1 => genToMain JFr_Data01.running
  | 2 => genToMain JFr_Data02.running
  | 3 => genToMain JFr_Data03.running
  | 4 => genToMain JFr_Data04.running
  | 5 => genToMain JFr_Data05.running
  | 6 => genToMain JFr_Data06.running
  | 7 => genToMain JFr_Data07.running
  | 8 => genToMain JFr_Data08.running
  | _ => genToMain JFr_Data09.running
def output (r : Fin 10) : MainQM := match r.val with
  | 0 => genToMain JFr_Data00.output
  | 1 => genToMain JFr_Data01.output
  | 2 => genToMain JFr_Data02.output
  | 3 => genToMain JFr_Data03.output
  | 4 => genToMain JFr_Data04.output
  | 5 => genToMain JFr_Data05.output
  | 6 => genToMain JFr_Data06.output
  | 7 => genToMain JFr_Data07.output
  | 8 => genToMain JFr_Data08.output
  | _ => genToMain JFr_Data09.output

theorem boundary (r : Fin 10) : generatedMainBoundary (polynomial r)=ok (running r) := by
  fin_cases r
  · exact JFr_Round00.boundary
  · exact JFr_Round01.boundary
  · exact JFr_Round02.boundary
  · exact JFr_Round03.boundary
  · exact JFr_Round04.boundary
  · exact JFr_Round05.boundary
  · exact JFr_Round06.boundary
  · exact JFr_Round07.boundary
  · exact JFr_Round08.boundary
  · exact JFr_Round09.boundary

theorem value (r : Fin 10) : generatedMainValue (polynomial r) (challenges r) (UScalar.ofNatCore r.val (by have := r.isLt;scalar_tac))=ok (output r) := by
  fin_cases r
  · exact JFr_Round00.value
  · exact JFr_Round01.value
  · exact JFr_Round02.value
  · exact JFr_Round03.value
  · exact JFr_Round04.value
  · exact JFr_Round05.value
  · exact JFr_Round06.value
  · exact JFr_Round07.value
  · exact JFr_Round08.value
  · exact JFr_Round09.value

theorem decoded (expanded : Slice U8) (pre : r1_wire.Prefix)
    (expand : compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded))
    (parse : PrefixAdapter.parseAccepted expanded=ok (.Ok pre)) (r : Fin 10) :
    ∃ vr,r1_wire.Prefix.validated_record pre (JFv_SemanticDecode.roundRow r)=ok (.Ok vr) ∧
      decodeMain 28#usize vr 0#usize=ok (.Ok (polynomial r)) := by
  have records := JFr_PrefixRecords.source expanded pre expand parse
  fin_cases r
  · refine ⟨JFr_Decode00.record,?_,JFr_Decode00.source⟩
    exact JFr_RecordsAt.source pre records 15#u8 (by change 15<27;omega) JFw_NativeRow15.record rfl
  · refine ⟨JFr_Decode01.record,?_,JFr_Decode01.source⟩
    exact JFr_RecordsAt.source pre records 16#u8 (by change 16<27;omega) JFw_NativeRow16.record rfl
  · refine ⟨JFr_Decode02.record,?_,JFr_Decode02.source⟩
    exact JFr_RecordsAt.source pre records 17#u8 (by change 17<27;omega) JFw_NativeRow17.record rfl
  · refine ⟨JFr_Decode03.record,?_,JFr_Decode03.source⟩
    exact JFr_RecordsAt.source pre records 18#u8 (by change 18<27;omega) JFw_NativeRow18.record rfl
  · refine ⟨JFr_Decode04.record,?_,JFr_Decode04.source⟩
    exact JFr_RecordsAt.source pre records 19#u8 (by change 19<27;omega) JFw_NativeRow19.record rfl
  · refine ⟨JFr_Decode05.record,?_,JFr_Decode05.source⟩
    exact JFr_RecordsAt.source pre records 20#u8 (by change 20<27;omega) JFw_NativeRow20.record rfl
  · refine ⟨JFr_Decode06.record,?_,JFr_Decode06.source⟩
    exact JFr_RecordsAt.source pre records 21#u8 (by change 21<27;omega) JFw_NativeRow21.record rfl
  · refine ⟨JFr_Decode07.record,?_,JFr_Decode07.source⟩
    exact JFr_RecordsAt.source pre records 22#u8 (by change 22<27;omega) JFw_NativeRow22.record rfl
  · refine ⟨JFr_Decode08.record,?_,JFr_Decode08.source⟩
    exact JFr_RecordsAt.source pre records 23#u8 (by change 23<27;omega) JFw_NativeRow23.record rfl
  · refine ⟨JFr_Decode09.record,?_,JFr_Decode09.source⟩
    exact JFr_RecordsAt.source pre records 24#u8 (by change 24<27;omega) JFw_NativeRow24.record rfl

#print axioms boundary
#print axioms value
#print axioms decoded
end AspisR1.JFr_RealRounds
end
