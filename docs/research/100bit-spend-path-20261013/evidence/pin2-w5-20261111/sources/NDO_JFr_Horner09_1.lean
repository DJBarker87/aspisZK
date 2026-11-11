import NDO_JFr_Data09
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner09_1
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data09
def initial : Q := (q 1913119858#u32 1966863962#u32 967324423#u32 1348006761#u32)
theorem mul13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1913119858#u32 1966863962#u32 967324423#u32 1348006761#u32) (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32)=ok (q 1800692295#u32 1924483195#u32 598247649#u32 1236630944#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1913119858 < 2147483647 ∧ 1966863962 < 2147483647) ∧ (967324423 < 2147483647 ∧ 1348006761 < 2147483647); omega) (by change (1088201115 < 2147483647 ∧ 1292966428 < 2147483647) ∧ (495022806 < 2147483647 ∧ 1713251341 < 2147483647); omega) (by rfl)
#print axioms mul13
theorem add13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1800692295#u32 1924483195#u32 598247649#u32 1236630944#u32) c13=ok (q 706563707#u32 1528646895#u32 2070411455#u32 24817917#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1800692295 < 2147483647 ∧ 1924483195 < 2147483647) ∧ (598247649 < 2147483647 ∧ 1236630944 < 2147483647); omega) canonical13 (by rfl)
#print axioms add13
theorem mul12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 706563707#u32 1528646895#u32 2070411455#u32 24817917#u32) (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32)=ok (q 687056554#u32 812332649#u32 1679534267#u32 1964827376#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (706563707 < 2147483647 ∧ 1528646895 < 2147483647) ∧ (2070411455 < 2147483647 ∧ 24817917 < 2147483647); omega) (by change (1088201115 < 2147483647 ∧ 1292966428 < 2147483647) ∧ (495022806 < 2147483647 ∧ 1713251341 < 2147483647); omega) (by rfl)
#print axioms mul12
theorem add12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 687056554#u32 812332649#u32 1679534267#u32 1964827376#u32) c12=ok (q 751447362#u32 1051842716#u32 310797457#u32 2088903363#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (687056554 < 2147483647 ∧ 812332649 < 2147483647) ∧ (1679534267 < 2147483647 ∧ 1964827376 < 2147483647); omega) canonical12 (by rfl)
#print axioms add12
theorem mul11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 751447362#u32 1051842716#u32 310797457#u32 2088903363#u32) (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32)=ok (q 55920554#u32 260284114#u32 971216389#u32 172941999#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (751447362 < 2147483647 ∧ 1051842716 < 2147483647) ∧ (310797457 < 2147483647 ∧ 2088903363 < 2147483647); omega) (by change (1088201115 < 2147483647 ∧ 1292966428 < 2147483647) ∧ (495022806 < 2147483647 ∧ 1713251341 < 2147483647); omega) (by rfl)
#print axioms mul11
theorem add11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 55920554#u32 260284114#u32 971216389#u32 172941999#u32) c11=ok (q 749444177#u32 832752622#u32 62690540#u32 828419883#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (55920554 < 2147483647 ∧ 260284114 < 2147483647) ∧ (971216389 < 2147483647 ∧ 172941999 < 2147483647); omega) canonical11 (by rfl)
#print axioms add11
theorem mul10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 749444177#u32 832752622#u32 62690540#u32 828419883#u32) (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32)=ok (q 633403392#u32 1514258940#u32 1716950944#u32 1785914516#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (749444177 < 2147483647 ∧ 832752622 < 2147483647) ∧ (62690540 < 2147483647 ∧ 828419883 < 2147483647); omega) (by change (1088201115 < 2147483647 ∧ 1292966428 < 2147483647) ∧ (495022806 < 2147483647 ∧ 1713251341 < 2147483647); omega) (by rfl)
#print axioms mul10
theorem add10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 633403392#u32 1514258940#u32 1716950944#u32 1785914516#u32) c10=ok (q 1339453946#u32 1637708444#u32 1546033156#u32 1816047206#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (633403392 < 2147483647 ∧ 1514258940 < 2147483647) ∧ (1716950944 < 2147483647 ∧ 1785914516 < 2147483647); omega) canonical10 (by rfl)
#print axioms add10
theorem mul09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1339453946#u32 1637708444#u32 1546033156#u32 1816047206#u32) (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32)=ok (q 1752998537#u32 1582064926#u32 1018679178#u32 909673743#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1339453946 < 2147483647 ∧ 1637708444 < 2147483647) ∧ (1546033156 < 2147483647 ∧ 1816047206 < 2147483647); omega) (by change (1088201115 < 2147483647 ∧ 1292966428 < 2147483647) ∧ (495022806 < 2147483647 ∧ 1713251341 < 2147483647); omega) (by rfl)
#print axioms mul09
theorem add09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1752998537#u32 1582064926#u32 1018679178#u32 909673743#u32) c09=ok (q 150404107#u32 760145928#u32 1347337048#u32 2127769685#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1752998537 < 2147483647 ∧ 1582064926 < 2147483647) ∧ (1018679178 < 2147483647 ∧ 909673743 < 2147483647); omega) canonical09 (by rfl)
#print axioms add09
theorem mul08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 150404107#u32 760145928#u32 1347337048#u32 2127769685#u32) (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32)=ok (q 1292791186#u32 1751883111#u32 962842897#u32 161083429#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (150404107 < 2147483647 ∧ 760145928 < 2147483647) ∧ (1347337048 < 2147483647 ∧ 2127769685 < 2147483647); omega) (by change (1088201115 < 2147483647 ∧ 1292966428 < 2147483647) ∧ (495022806 < 2147483647 ∧ 1713251341 < 2147483647); omega) (by rfl)
#print axioms mul08
theorem add08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1292791186#u32 1751883111#u32 962842897#u32 161083429#u32) c08=ok (q 1029962050#u32 1354056521#u32 1263704848#u32 1562423806#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1292791186 < 2147483647 ∧ 1751883111 < 2147483647) ∧ (962842897 < 2147483647 ∧ 161083429 < 2147483647); omega) canonical08 (by rfl)
#print axioms add08
theorem mul07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1029962050#u32 1354056521#u32 1263704848#u32 1562423806#u32) (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32)=ok (q 76365882#u32 1981543468#u32 775622921#u32 1361000955#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1029962050 < 2147483647 ∧ 1354056521 < 2147483647) ∧ (1263704848 < 2147483647 ∧ 1562423806 < 2147483647); omega) (by change (1088201115 < 2147483647 ∧ 1292966428 < 2147483647) ∧ (495022806 < 2147483647 ∧ 1713251341 < 2147483647); omega) (by rfl)
#print axioms mul07
theorem add07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 76365882#u32 1981543468#u32 775622921#u32 1361000955#u32) c07=ok (q 1545352746#u32 681258522#u32 594575768#u32 1916782464#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (76365882 < 2147483647 ∧ 1981543468 < 2147483647) ∧ (775622921 < 2147483647 ∧ 1361000955 < 2147483647); omega) canonical07 (by rfl)
#print axioms add07
theorem mul06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1545352746#u32 681258522#u32 594575768#u32 1916782464#u32) (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32)=ok (q 389735553#u32 332414239#u32 368656573#u32 1896566201#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1545352746 < 2147483647 ∧ 681258522 < 2147483647) ∧ (594575768 < 2147483647 ∧ 1916782464 < 2147483647); omega) (by change (1088201115 < 2147483647 ∧ 1292966428 < 2147483647) ∧ (495022806 < 2147483647 ∧ 1713251341 < 2147483647); omega) (by rfl)
#print axioms mul06
theorem add06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 389735553#u32 332414239#u32 368656573#u32 1896566201#u32) c06=ok (q 1383023057#u32 558687036#u32 404351880#u32 2132445932#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (389735553 < 2147483647 ∧ 332414239 < 2147483647) ∧ (368656573 < 2147483647 ∧ 1896566201 < 2147483647); omega) canonical06 (by rfl)
#print axioms add06
theorem mul05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1383023057#u32 558687036#u32 404351880#u32 2132445932#u32) (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32)=ok (q 1512172201#u32 1404455747#u32 2027887214#u32 612293050#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1383023057 < 2147483647 ∧ 558687036 < 2147483647) ∧ (404351880 < 2147483647 ∧ 2132445932 < 2147483647); omega) (by change (1088201115 < 2147483647 ∧ 1292966428 < 2147483647) ∧ (495022806 < 2147483647 ∧ 1713251341 < 2147483647); omega) (by rfl)
#print axioms mul05
theorem add05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1512172201#u32 1404455747#u32 2027887214#u32 612293050#u32) c05=ok (q 1234436400#u32 923523715#u32 1414147500#u32 1054231548#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1512172201 < 2147483647 ∧ 1404455747 < 2147483647) ∧ (2027887214 < 2147483647 ∧ 612293050 < 2147483647); omega) canonical05 (by rfl)
#print axioms add05
theorem mul04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1234436400#u32 923523715#u32 1414147500#u32 1054231548#u32) (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32)=ok (q 1257679450#u32 1479077698#u32 238903256#u32 1271511732#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1234436400 < 2147483647 ∧ 923523715 < 2147483647) ∧ (1414147500 < 2147483647 ∧ 1054231548 < 2147483647); omega) (by change (1088201115 < 2147483647 ∧ 1292966428 < 2147483647) ∧ (495022806 < 2147483647 ∧ 1713251341 < 2147483647); omega) (by rfl)
#print axioms mul04
theorem add04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1257679450#u32 1479077698#u32 238903256#u32 1271511732#u32) c04=ok (q 586704931#u32 1850434406#u32 1461451925#u32 583845773#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1257679450 < 2147483647 ∧ 1479077698 < 2147483647) ∧ (238903256 < 2147483647 ∧ 1271511732 < 2147483647); omega) canonical04 (by rfl)
#print axioms add04
theorem mul03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 586704931#u32 1850434406#u32 1461451925#u32 583845773#u32) (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32)=ok (q 297508763#u32 270882887#u32 2012849222#u32 1320591954#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (586704931 < 2147483647 ∧ 1850434406 < 2147483647) ∧ (1461451925 < 2147483647 ∧ 583845773 < 2147483647); omega) (by change (1088201115 < 2147483647 ∧ 1292966428 < 2147483647) ∧ (495022806 < 2147483647 ∧ 1713251341 < 2147483647); omega) (by rfl)
#print axioms mul03
theorem add03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 297508763#u32 270882887#u32 2012849222#u32 1320591954#u32) c03=ok (q 143769387#u32 1069911573#u32 536700980#u32 1350989545#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (297508763 < 2147483647 ∧ 270882887 < 2147483647) ∧ (2012849222 < 2147483647 ∧ 1320591954 < 2147483647); omega) canonical03 (by rfl)
#print axioms add03
theorem mul02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 143769387#u32 1069911573#u32 536700980#u32 1350989545#u32) (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32)=ok (q 350715169#u32 1952016156#u32 1113676158#u32 421216003#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (143769387 < 2147483647 ∧ 1069911573 < 2147483647) ∧ (536700980 < 2147483647 ∧ 1350989545 < 2147483647); omega) (by change (1088201115 < 2147483647 ∧ 1292966428 < 2147483647) ∧ (495022806 < 2147483647 ∧ 1713251341 < 2147483647); omega) (by rfl)
#print axioms mul02
theorem add02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 350715169#u32 1952016156#u32 1113676158#u32 421216003#u32) c02=ok (q 1184295832#u32 30236972#u32 848489060#u32 1376579843#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (350715169 < 2147483647 ∧ 1952016156 < 2147483647) ∧ (1113676158 < 2147483647 ∧ 421216003 < 2147483647); omega) canonical02 (by rfl)
#print axioms add02
theorem mul01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1184295832#u32 30236972#u32 848489060#u32 1376579843#u32) (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32)=ok (q 457967537#u32 724937134#u32 2041513700#u32 771689225#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1184295832 < 2147483647 ∧ 30236972 < 2147483647) ∧ (848489060 < 2147483647 ∧ 1376579843 < 2147483647); omega) (by change (1088201115 < 2147483647 ∧ 1292966428 < 2147483647) ∧ (495022806 < 2147483647 ∧ 1713251341 < 2147483647); omega) (by rfl)
#print axioms mul01
theorem add01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 457967537#u32 724937134#u32 2041513700#u32 771689225#u32) c01=ok (q 1175958620#u32 177575784#u32 54219397#u32 610406505#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (457967537 < 2147483647 ∧ 724937134 < 2147483647) ∧ (2041513700 < 2147483647 ∧ 771689225 < 2147483647); omega) canonical01 (by rfl)
#print axioms add01
theorem mul00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1175958620#u32 177575784#u32 54219397#u32 610406505#u32) (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32)=ok (q 1425211440#u32 804601766#u32 2023457431#u32 1922651437#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1175958620 < 2147483647 ∧ 177575784 < 2147483647) ∧ (54219397 < 2147483647 ∧ 610406505 < 2147483647); omega) (by change (1088201115 < 2147483647 ∧ 1292966428 < 2147483647) ∧ (495022806 < 2147483647 ∧ 1713251341 < 2147483647); omega) (by rfl)
#print axioms mul00
theorem add00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1425211440#u32 804601766#u32 2023457431#u32 1922651437#u32) c00=ok (q 427577454#u32 562351846#u32 2017191275#u32 1723272728#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1425211440 < 2147483647 ∧ 804601766 < 2147483647) ∧ (2023457431 < 2147483647 ∧ 1922651437 < 2147483647); omega) canonical00 (by rfl)
#print axioms add00
def final : Q := (q 427577454#u32 562351846#u32 2017191275#u32 1723272728#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 9#usize 14#usize initial 0#usize final := by
  refine .step (by change 14>0; omega) (JFr_IndexArithmetic.sub 14#usize 13#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32) from rfl) mul13 (show Array.index_usize p 13#usize=ok c13 from rfl) add13 ?_
  refine .step (by change 13>0; omega) (JFr_IndexArithmetic.sub 13#usize 12#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32) from rfl) mul12 (show Array.index_usize p 12#usize=ok c12 from rfl) add12 ?_
  refine .step (by change 12>0; omega) (JFr_IndexArithmetic.sub 12#usize 11#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32) from rfl) mul11 (show Array.index_usize p 11#usize=ok c11 from rfl) add11 ?_
  refine .step (by change 11>0; omega) (JFr_IndexArithmetic.sub 11#usize 10#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32) from rfl) mul10 (show Array.index_usize p 10#usize=ok c10 from rfl) add10 ?_
  refine .step (by change 10>0; omega) (JFr_IndexArithmetic.sub 10#usize 9#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32) from rfl) mul09 (show Array.index_usize p 9#usize=ok c09 from rfl) add09 ?_
  refine .step (by change 9>0; omega) (JFr_IndexArithmetic.sub 9#usize 8#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32) from rfl) mul08 (show Array.index_usize p 8#usize=ok c08 from rfl) add08 ?_
  refine .step (by change 8>0; omega) (JFr_IndexArithmetic.sub 8#usize 7#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32) from rfl) mul07 (show Array.index_usize p 7#usize=ok c07 from rfl) add07 ?_
  refine .step (by change 7>0; omega) (JFr_IndexArithmetic.sub 7#usize 6#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32) from rfl) mul06 (show Array.index_usize p 6#usize=ok c06 from rfl) add06 ?_
  refine .step (by change 6>0; omega) (JFr_IndexArithmetic.sub 6#usize 5#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32) from rfl) mul05 (show Array.index_usize p 5#usize=ok c05 from rfl) add05 ?_
  refine .step (by change 5>0; omega) (JFr_IndexArithmetic.sub 5#usize 4#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32) from rfl) mul04 (show Array.index_usize p 4#usize=ok c04 from rfl) add04 ?_
  refine .step (by change 4>0; omega) (JFr_IndexArithmetic.sub 4#usize 3#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32) from rfl) mul03 (show Array.index_usize p 3#usize=ok c03 from rfl) add03 ?_
  refine .step (by change 3>0; omega) (JFr_IndexArithmetic.sub 3#usize 2#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32) from rfl) mul02 (show Array.index_usize p 2#usize=ok c02 from rfl) add02 ?_
  refine .step (by change 2>0; omega) (JFr_IndexArithmetic.sub 2#usize 1#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32) from rfl) mul01 (show Array.index_usize p 1#usize=ok c01 from rfl) add01 ?_
  refine .step (by change 1>0; omega) (JFr_IndexArithmetic.sub 1#usize 0#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32) from rfl) mul00 (show Array.index_usize p 0#usize=ok c00 from rfl) add00 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner09_1
