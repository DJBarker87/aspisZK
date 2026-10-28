import NDO_JFz_Row00
import NDO_JFz_Row01
import NDO_JFz_Row02
import NDO_JFz_Row03
import NDO_JFz_Row04
import NDO_JFz_Row05
import NDO_JFz_Row06
import NDO_JFz_Row07
import NDO_JFz_Row08
import NDO_JFz_Row09
import NDO_JFz_Row10
import NDO_JFz_Row11
import NDO_JFz_Row12
import NDO_JFz_Row13
import NDO_JFz_Row14
import NDO_JFz_Row15
import NDO_JFz_Row16
import NDO_JFz_Row17
import NDO_JFz_Row18
import NDO_JFz_Row19
import NDO_JFz_Row20
import NDO_JFz_Row21
import NDO_JFz_Row22
import NDO_JFz_Row23
import NDO_JFz_Row24
import NDO_JFz_Row25
import NDO_JFz_Row26
import NDO_JFz_ScanAccepted
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_Parsed
open AspisV8R19.DuplexFrames OraclePortCompactDraft JFz_RowGeometry
def rows27 : List Bytes := []
def rows26 : List Bytes := PSem_Rows.expandedRow 26 (slice wire 6562 469) :: rows27
def rows25 : List Bytes := PSem_Rows.expandedRow 25 (slice wire 4701 2330) :: rows26
def rows24 : List Bytes := PSem_Rows.expandedRow 24 (slice wire 4248 2783) :: rows25
def rows23 : List Bytes := PSem_Rows.expandedRow 23 (slice wire 3795 3236) :: rows24
def rows22 : List Bytes := PSem_Rows.expandedRow 22 (slice wire 3342 3689) :: rows23
def rows21 : List Bytes := PSem_Rows.expandedRow 21 (slice wire 2889 4142) :: rows22
def rows20 : List Bytes := PSem_Rows.expandedRow 20 (slice wire 2436 4595) :: rows21
def rows19 : List Bytes := PSem_Rows.expandedRow 19 (slice wire 1983 5048) :: rows20
def rows18 : List Bytes := PSem_Rows.expandedRow 18 (slice wire 1530 5501) :: rows19
def rows17 : List Bytes := PSem_Rows.expandedRow 17 (slice wire 1077 5954) :: rows18
def rows16 : List Bytes := PSem_Rows.expandedRow 16 (slice wire 624 6407) :: rows17
def rows15 : List Bytes := PSem_Rows.expandedRow 15 (slice wire 171 6860) :: rows16
def rows14 : List Bytes := PSem_Rows.expandedRow 14 (slice wire 150 6881) :: rows15
def rows13 : List Bytes := PSem_Rows.expandedRow 13 (slice wire 145 6886) :: rows14
def rows12 : List Bytes := PSem_Rows.expandedRow 12 (slice wire 140 6891) :: rows13
def rows11 : List Bytes := PSem_Rows.expandedRow 11 (slice wire 135 6896) :: rows12
def rows10 : List Bytes := PSem_Rows.expandedRow 10 (slice wire 130 6901) :: rows11
def rows09 : List Bytes := PSem_Rows.expandedRow 9 (slice wire 125 6906) :: rows10
def rows08 : List Bytes := PSem_Rows.expandedRow 8 (slice wire 120 6911) :: rows09
def rows07 : List Bytes := PSem_Rows.expandedRow 7 (slice wire 115 6916) :: rows08
def rows06 : List Bytes := PSem_Rows.expandedRow 6 (slice wire 110 6921) :: rows07
def rows05 : List Bytes := PSem_Rows.expandedRow 5 (slice wire 105 6926) :: rows06
def rows04 : List Bytes := PSem_Rows.expandedRow 4 (slice wire 100 6931) :: rows05
def rows03 : List Bytes := PSem_Rows.expandedRow 3 (slice wire 95 6936) :: rows04
def rows02 : List Bytes := PSem_Rows.expandedRow 2 (slice wire 58 6973) :: rows03
def rows01 : List Bytes := PSem_Rows.expandedRow 1 (slice wire 53 6978) :: rows02
def rows00 : List Bytes := PSem_Rows.expandedRow 0 (slice wire 48 6983) :: rows01
theorem end_rows : semanticRows 0 27 (slice wire 7031 0) = some rows27 := by
  simp only [semanticRows,slice,List.take_zero,if_true,rows27]
theorem accepted26 : semanticRows 1 26 (slice wire 6562 469) = some rows26 :=
  JFz_Row26.step _ end_rows
#print axioms accepted26
theorem accepted25 : semanticRows 2 25 (slice wire 4701 2330) = some rows25 :=
  JFz_Row25.step _ accepted26
#print axioms accepted25
theorem accepted24 : semanticRows 3 24 (slice wire 4248 2783) = some rows24 :=
  JFz_Row24.step _ accepted25
#print axioms accepted24
theorem accepted23 : semanticRows 4 23 (slice wire 3795 3236) = some rows23 :=
  JFz_Row23.step _ accepted24
#print axioms accepted23
theorem accepted22 : semanticRows 5 22 (slice wire 3342 3689) = some rows22 :=
  JFz_Row22.step _ accepted23
#print axioms accepted22
theorem accepted21 : semanticRows 6 21 (slice wire 2889 4142) = some rows21 :=
  JFz_Row21.step _ accepted22
#print axioms accepted21
theorem accepted20 : semanticRows 7 20 (slice wire 2436 4595) = some rows20 :=
  JFz_Row20.step _ accepted21
#print axioms accepted20
theorem accepted19 : semanticRows 8 19 (slice wire 1983 5048) = some rows19 :=
  JFz_Row19.step _ accepted20
#print axioms accepted19
theorem accepted18 : semanticRows 9 18 (slice wire 1530 5501) = some rows18 :=
  JFz_Row18.step _ accepted19
#print axioms accepted18
theorem accepted17 : semanticRows 10 17 (slice wire 1077 5954) = some rows17 :=
  JFz_Row17.step _ accepted18
#print axioms accepted17
theorem accepted16 : semanticRows 11 16 (slice wire 624 6407) = some rows16 :=
  JFz_Row16.step _ accepted17
#print axioms accepted16
theorem accepted15 : semanticRows 12 15 (slice wire 171 6860) = some rows15 :=
  JFz_Row15.step _ accepted16
#print axioms accepted15
theorem accepted14 : semanticRows 13 14 (slice wire 150 6881) = some rows14 :=
  JFz_Row14.step _ accepted15
#print axioms accepted14
theorem accepted13 : semanticRows 14 13 (slice wire 145 6886) = some rows13 :=
  JFz_Row13.step _ accepted14
#print axioms accepted13
theorem accepted12 : semanticRows 15 12 (slice wire 140 6891) = some rows12 :=
  JFz_Row12.step _ accepted13
#print axioms accepted12
theorem accepted11 : semanticRows 16 11 (slice wire 135 6896) = some rows11 :=
  JFz_Row11.step _ accepted12
#print axioms accepted11
theorem accepted10 : semanticRows 17 10 (slice wire 130 6901) = some rows10 :=
  JFz_Row10.step _ accepted11
#print axioms accepted10
theorem accepted09 : semanticRows 18 9 (slice wire 125 6906) = some rows09 :=
  JFz_Row09.step _ accepted10
#print axioms accepted09
theorem accepted08 : semanticRows 19 8 (slice wire 120 6911) = some rows08 :=
  JFz_Row08.step _ accepted09
#print axioms accepted08
theorem accepted07 : semanticRows 20 7 (slice wire 115 6916) = some rows07 :=
  JFz_Row07.step _ accepted08
#print axioms accepted07
theorem accepted06 : semanticRows 21 6 (slice wire 110 6921) = some rows06 :=
  JFz_Row06.step _ accepted07
#print axioms accepted06
theorem accepted05 : semanticRows 22 5 (slice wire 105 6926) = some rows05 :=
  JFz_Row05.step _ accepted06
#print axioms accepted05
theorem accepted04 : semanticRows 23 4 (slice wire 100 6931) = some rows04 :=
  JFz_Row04.step _ accepted05
#print axioms accepted04
theorem accepted03 : semanticRows 24 3 (slice wire 95 6936) = some rows03 :=
  JFz_Row03.step _ accepted04
#print axioms accepted03
theorem accepted02 : semanticRows 25 2 (slice wire 58 6973) = some rows02 :=
  JFz_Row02.step _ accepted03
#print axioms accepted02
theorem accepted01 : semanticRows 26 1 (slice wire 53 6978) = some rows01 :=
  JFz_Row01.step _ accepted02
#print axioms accepted01
theorem accepted00 : semanticRows 27 0 (slice wire 48 6983) = some rows00 :=
  JFz_Row00.step _ accepted01
#print axioms accepted00
theorem header : OraclePortHeader.accepts wire = true :=
  (Op3I_Install.header_of_success JFx_NativeBytes.proof .S2 JFx_HeaderFields.shape_accepted).2
theorem parsed : parse wire = some ⟨wire,rows00⟩ := by
  have scanned : scan wire := JFz_ScanAccepted.scan_accepted
  simp only [parse,header,Bool.true_eq_false,if_false,scanned,not_true_eq_false,
    accepted00,Option.bind_some,Option.pure_def]
  rfl
#print axioms end_rows
#print axioms header
#print axioms parsed
end AspisR1.JFz_Parsed
end
