import NDO_JFr_Data01
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner01_1
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data01
def initial : Q := (q 1320941510#u32 154334066#u32 1332945878#u32 1627398046#u32)
theorem mul13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1320941510#u32 154334066#u32 1332945878#u32 1627398046#u32) (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32)=ok (q 941019764#u32 1305122451#u32 261393621#u32 150564738#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1320941510 < 2147483647 ∧ 154334066 < 2147483647) ∧ (1332945878 < 2147483647 ∧ 1627398046 < 2147483647); omega) (by change (1938229017 < 2147483647 ∧ 474903281 < 2147483647) ∧ (2119643323 < 2147483647 ∧ 1456121415 < 2147483647); omega) (by rfl)
#print axioms mul13
theorem add13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 941019764#u32 1305122451#u32 261393621#u32 150564738#u32) c13=ok (q 1404449338#u32 1103627935#u32 657505023#u32 231395396#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (941019764 < 2147483647 ∧ 1305122451 < 2147483647) ∧ (261393621 < 2147483647 ∧ 150564738 < 2147483647); omega) canonical13 (by rfl)
#print axioms add13
theorem mul12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1404449338#u32 1103627935#u32 657505023#u32 231395396#u32) (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32)=ok (q 771338438#u32 10966121#u32 1044948935#u32 1396904971#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1404449338 < 2147483647 ∧ 1103627935 < 2147483647) ∧ (657505023 < 2147483647 ∧ 231395396 < 2147483647); omega) (by change (1938229017 < 2147483647 ∧ 474903281 < 2147483647) ∧ (2119643323 < 2147483647 ∧ 1456121415 < 2147483647); omega) (by rfl)
#print axioms mul12
theorem add12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 771338438#u32 10966121#u32 1044948935#u32 1396904971#u32) c12=ok (q 618469051#u32 118062900#u32 224441707#u32 2056025483#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (771338438 < 2147483647 ∧ 10966121 < 2147483647) ∧ (1044948935 < 2147483647 ∧ 1396904971 < 2147483647); omega) canonical12 (by rfl)
#print axioms add12
theorem mul11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 618469051#u32 118062900#u32 224441707#u32 2056025483#u32) (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32)=ok (q 433951861#u32 1685077160#u32 61351229#u32 121491902#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (618469051 < 2147483647 ∧ 118062900 < 2147483647) ∧ (224441707 < 2147483647 ∧ 2056025483 < 2147483647); omega) (by change (1938229017 < 2147483647 ∧ 474903281 < 2147483647) ∧ (2119643323 < 2147483647 ∧ 1456121415 < 2147483647); omega) (by rfl)
#print axioms mul11
theorem add11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 433951861#u32 1685077160#u32 61351229#u32 121491902#u32) c11=ok (q 1475721214#u32 108243139#u32 92413110#u32 2058201122#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (433951861 < 2147483647 ∧ 1685077160 < 2147483647) ∧ (61351229 < 2147483647 ∧ 121491902 < 2147483647); omega) canonical11 (by rfl)
#print axioms add11
theorem mul10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1475721214#u32 108243139#u32 92413110#u32 2058201122#u32) (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32)=ok (q 661938918#u32 1028620210#u32 1593412124#u32 460381421#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1475721214 < 2147483647 ∧ 108243139 < 2147483647) ∧ (92413110 < 2147483647 ∧ 2058201122 < 2147483647); omega) (by change (1938229017 < 2147483647 ∧ 474903281 < 2147483647) ∧ (2119643323 < 2147483647 ∧ 1456121415 < 2147483647); omega) (by rfl)
#print axioms mul10
theorem add10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 661938918#u32 1028620210#u32 1593412124#u32 460381421#u32) c10=ok (q 1194365764#u32 1557634596#u32 1529473083#u32 141840835#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (661938918 < 2147483647 ∧ 1028620210 < 2147483647) ∧ (1593412124 < 2147483647 ∧ 460381421 < 2147483647); omega) canonical10 (by rfl)
#print axioms add10
theorem mul09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1194365764#u32 1557634596#u32 1529473083#u32 141840835#u32) (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32)=ok (q 1998264160#u32 1765346703#u32 208158815#u32 284866356#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1194365764 < 2147483647 ∧ 1557634596 < 2147483647) ∧ (1529473083 < 2147483647 ∧ 141840835 < 2147483647); omega) (by change (1938229017 < 2147483647 ∧ 474903281 < 2147483647) ∧ (2119643323 < 2147483647 ∧ 1456121415 < 2147483647); omega) (by rfl)
#print axioms mul09
theorem add09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1998264160#u32 1765346703#u32 208158815#u32 284866356#u32) c09=ok (q 1051918244#u32 1773404422#u32 285233530#u32 1747206923#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1998264160 < 2147483647 ∧ 1765346703 < 2147483647) ∧ (208158815 < 2147483647 ∧ 284866356 < 2147483647); omega) canonical09 (by rfl)
#print axioms add09
theorem mul08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1051918244#u32 1773404422#u32 285233530#u32 1747206923#u32) (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32)=ok (q 1308278473#u32 1743001932#u32 652258560#u32 1125164447#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1051918244 < 2147483647 ∧ 1773404422 < 2147483647) ∧ (285233530 < 2147483647 ∧ 1747206923 < 2147483647); omega) (by change (1938229017 < 2147483647 ∧ 474903281 < 2147483647) ∧ (2119643323 < 2147483647 ∧ 1456121415 < 2147483647); omega) (by rfl)
#print axioms mul08
theorem add08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1308278473#u32 1743001932#u32 652258560#u32 1125164447#u32) c08=ok (q 1226977803#u32 798552652#u32 2016902537#u32 1903219477#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1308278473 < 2147483647 ∧ 1743001932 < 2147483647) ∧ (652258560 < 2147483647 ∧ 1125164447 < 2147483647); omega) canonical08 (by rfl)
#print axioms add08
theorem mul07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1226977803#u32 798552652#u32 2016902537#u32 1903219477#u32) (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32)=ok (q 1303801786#u32 1027568923#u32 2120869658#u32 1038235630#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1226977803 < 2147483647 ∧ 798552652 < 2147483647) ∧ (2016902537 < 2147483647 ∧ 1903219477 < 2147483647); omega) (by change (1938229017 < 2147483647 ∧ 474903281 < 2147483647) ∧ (2119643323 < 2147483647 ∧ 1456121415 < 2147483647); omega) (by rfl)
#print axioms mul07
theorem add07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1303801786#u32 1027568923#u32 2120869658#u32 1038235630#u32) c07=ok (q 740204323#u32 736006969#u32 2077314245#u32 1586993426#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1303801786 < 2147483647 ∧ 1027568923 < 2147483647) ∧ (2120869658 < 2147483647 ∧ 1038235630 < 2147483647); omega) canonical07 (by rfl)
#print axioms add07
theorem mul06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 740204323#u32 736006969#u32 2077314245#u32 1586993426#u32) (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32)=ok (q 837272020#u32 882969206#u32 27295984#u32 1737461556#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (740204323 < 2147483647 ∧ 736006969 < 2147483647) ∧ (2077314245 < 2147483647 ∧ 1586993426 < 2147483647); omega) (by change (1938229017 < 2147483647 ∧ 474903281 < 2147483647) ∧ (2119643323 < 2147483647 ∧ 1456121415 < 2147483647); omega) (by rfl)
#print axioms mul06
theorem add06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 837272020#u32 882969206#u32 27295984#u32 1737461556#u32) c06=ok (q 459783140#u32 2058548214#u32 451657160#u32 1026375697#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (837272020 < 2147483647 ∧ 882969206 < 2147483647) ∧ (27295984 < 2147483647 ∧ 1737461556 < 2147483647); omega) canonical06 (by rfl)
#print axioms add06
theorem mul05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 459783140#u32 2058548214#u32 451657160#u32 1026375697#u32) (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32)=ok (q 100371661#u32 474494230#u32 126617891#u32 1391644399#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (459783140 < 2147483647 ∧ 2058548214 < 2147483647) ∧ (451657160 < 2147483647 ∧ 1026375697 < 2147483647); omega) (by change (1938229017 < 2147483647 ∧ 474903281 < 2147483647) ∧ (2119643323 < 2147483647 ∧ 1456121415 < 2147483647); omega) (by rfl)
#print axioms mul05
theorem add05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 100371661#u32 474494230#u32 126617891#u32 1391644399#u32) c05=ok (q 338967611#u32 1749734368#u32 795209089#u32 165970321#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (100371661 < 2147483647 ∧ 474494230 < 2147483647) ∧ (126617891 < 2147483647 ∧ 1391644399 < 2147483647); omega) canonical05 (by rfl)
#print axioms add05
theorem mul04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 338967611#u32 1749734368#u32 795209089#u32 165970321#u32) (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32)=ok (q 1908080264#u32 97392610#u32 1491634859#u32 2063679092#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (338967611 < 2147483647 ∧ 1749734368 < 2147483647) ∧ (795209089 < 2147483647 ∧ 165970321 < 2147483647); omega) (by change (1938229017 < 2147483647 ∧ 474903281 < 2147483647) ∧ (2119643323 < 2147483647 ∧ 1456121415 < 2147483647); omega) (by rfl)
#print axioms mul04
theorem add04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1908080264#u32 97392610#u32 1491634859#u32 2063679092#u32) c04=ok (q 1901248835#u32 987615693#u32 609449410#u32 646852475#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1908080264 < 2147483647 ∧ 97392610 < 2147483647) ∧ (1491634859 < 2147483647 ∧ 2063679092 < 2147483647); omega) canonical04 (by rfl)
#print axioms add04
theorem mul03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1901248835#u32 987615693#u32 609449410#u32 646852475#u32) (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32)=ok (q 943441791#u32 841524078#u32 1267265937#u32 2082300756#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1901248835 < 2147483647 ∧ 987615693 < 2147483647) ∧ (609449410 < 2147483647 ∧ 646852475 < 2147483647); omega) (by change (1938229017 < 2147483647 ∧ 474903281 < 2147483647) ∧ (2119643323 < 2147483647 ∧ 1456121415 < 2147483647); omega) (by rfl)
#print axioms mul03
theorem add03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 943441791#u32 841524078#u32 1267265937#u32 2082300756#u32) c03=ok (q 1124828556#u32 988411521#u32 711083132#u32 1043453425#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (943441791 < 2147483647 ∧ 841524078 < 2147483647) ∧ (1267265937 < 2147483647 ∧ 2082300756 < 2147483647); omega) canonical03 (by rfl)
#print axioms add03
theorem mul02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1124828556#u32 988411521#u32 711083132#u32 1043453425#u32) (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32)=ok (q 337732031#u32 862438834#u32 377268650#u32 1760521365#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1124828556 < 2147483647 ∧ 988411521 < 2147483647) ∧ (711083132 < 2147483647 ∧ 1043453425 < 2147483647); omega) (by change (1938229017 < 2147483647 ∧ 474903281 < 2147483647) ∧ (2119643323 < 2147483647 ∧ 1456121415 < 2147483647); omega) (by rfl)
#print axioms mul02
theorem add02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 337732031#u32 862438834#u32 377268650#u32 1760521365#u32) c02=ok (q 15360478#u32 1378363469#u32 839738177#u32 29015046#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (337732031 < 2147483647 ∧ 862438834 < 2147483647) ∧ (377268650 < 2147483647 ∧ 1760521365 < 2147483647); omega) canonical02 (by rfl)
#print axioms add02
theorem mul01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 15360478#u32 1378363469#u32 839738177#u32 29015046#u32) (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32)=ok (q 1877467191#u32 411506667#u32 753533675#u32 422543220#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (15360478 < 2147483647 ∧ 1378363469 < 2147483647) ∧ (839738177 < 2147483647 ∧ 29015046 < 2147483647); omega) (by change (1938229017 < 2147483647 ∧ 474903281 < 2147483647) ∧ (2119643323 < 2147483647 ∧ 1456121415 < 2147483647); omega) (by rfl)
#print axioms mul01
theorem add01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1877467191#u32 411506667#u32 753533675#u32 422543220#u32) c01=ok (q 891350277#u32 282916772#u32 1038895896#u32 311070091#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1877467191 < 2147483647 ∧ 411506667 < 2147483647) ∧ (753533675 < 2147483647 ∧ 422543220 < 2147483647); omega) canonical01 (by rfl)
#print axioms add01
theorem mul00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 891350277#u32 282916772#u32 1038895896#u32 311070091#u32) (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32)=ok (q 1004144048#u32 708884778#u32 1303332518#u32 1918405454#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (891350277 < 2147483647 ∧ 282916772 < 2147483647) ∧ (1038895896 < 2147483647 ∧ 311070091 < 2147483647); omega) (by change (1938229017 < 2147483647 ∧ 474903281 < 2147483647) ∧ (2119643323 < 2147483647 ∧ 1456121415 < 2147483647); omega) (by rfl)
#print axioms mul00
theorem add00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1004144048#u32 708884778#u32 1303332518#u32 1918405454#u32) c00=ok (q 1105204357#u32 2021421100#u32 1958527491#u32 1586288520#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1004144048 < 2147483647 ∧ 708884778 < 2147483647) ∧ (1303332518 < 2147483647 ∧ 1918405454 < 2147483647); omega) canonical00 (by rfl)
#print axioms add00
def final : Q := (q 1105204357#u32 2021421100#u32 1958527491#u32 1586288520#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 1#usize 14#usize initial 0#usize final := by
  refine .step (by change 14>0; omega) (JFr_IndexArithmetic.sub 14#usize 13#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32) from rfl) mul13 (show Array.index_usize p 13#usize=ok c13 from rfl) add13 ?_
  refine .step (by change 13>0; omega) (JFr_IndexArithmetic.sub 13#usize 12#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32) from rfl) mul12 (show Array.index_usize p 12#usize=ok c12 from rfl) add12 ?_
  refine .step (by change 12>0; omega) (JFr_IndexArithmetic.sub 12#usize 11#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32) from rfl) mul11 (show Array.index_usize p 11#usize=ok c11 from rfl) add11 ?_
  refine .step (by change 11>0; omega) (JFr_IndexArithmetic.sub 11#usize 10#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32) from rfl) mul10 (show Array.index_usize p 10#usize=ok c10 from rfl) add10 ?_
  refine .step (by change 10>0; omega) (JFr_IndexArithmetic.sub 10#usize 9#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32) from rfl) mul09 (show Array.index_usize p 9#usize=ok c09 from rfl) add09 ?_
  refine .step (by change 9>0; omega) (JFr_IndexArithmetic.sub 9#usize 8#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32) from rfl) mul08 (show Array.index_usize p 8#usize=ok c08 from rfl) add08 ?_
  refine .step (by change 8>0; omega) (JFr_IndexArithmetic.sub 8#usize 7#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32) from rfl) mul07 (show Array.index_usize p 7#usize=ok c07 from rfl) add07 ?_
  refine .step (by change 7>0; omega) (JFr_IndexArithmetic.sub 7#usize 6#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32) from rfl) mul06 (show Array.index_usize p 6#usize=ok c06 from rfl) add06 ?_
  refine .step (by change 6>0; omega) (JFr_IndexArithmetic.sub 6#usize 5#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32) from rfl) mul05 (show Array.index_usize p 5#usize=ok c05 from rfl) add05 ?_
  refine .step (by change 5>0; omega) (JFr_IndexArithmetic.sub 5#usize 4#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32) from rfl) mul04 (show Array.index_usize p 4#usize=ok c04 from rfl) add04 ?_
  refine .step (by change 4>0; omega) (JFr_IndexArithmetic.sub 4#usize 3#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32) from rfl) mul03 (show Array.index_usize p 3#usize=ok c03 from rfl) add03 ?_
  refine .step (by change 3>0; omega) (JFr_IndexArithmetic.sub 3#usize 2#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32) from rfl) mul02 (show Array.index_usize p 2#usize=ok c02 from rfl) add02 ?_
  refine .step (by change 2>0; omega) (JFr_IndexArithmetic.sub 2#usize 1#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32) from rfl) mul01 (show Array.index_usize p 1#usize=ok c01 from rfl) add01 ?_
  refine .step (by change 1>0; omega) (JFr_IndexArithmetic.sub 1#usize 0#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32) from rfl) mul00 (show Array.index_usize p 0#usize=ok c00 from rfl) add00 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner01_1
