import NDO_JFr_Data05
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner05_1
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data05
def initial : Q := (q 2094586920#u32 1154417908#u32 1213740484#u32 1672019413#u32)
theorem mul13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2094586920#u32 1154417908#u32 1213740484#u32 1672019413#u32) (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32)=ok (q 432395655#u32 2078456333#u32 856402910#u32 1203290467#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2094586920 < 2147483647 ∧ 1154417908 < 2147483647) ∧ (1213740484 < 2147483647 ∧ 1672019413 < 2147483647); omega) (by change (810819047 < 2147483647 ∧ 1156380883 < 2147483647) ∧ (768810467 < 2147483647 ∧ 1018558903 < 2147483647); omega) (by rfl)
#print axioms mul13
theorem add13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 432395655#u32 2078456333#u32 856402910#u32 1203290467#u32) c13=ok (q 1184276229#u32 853882849#u32 1036962464#u32 395885796#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (432395655 < 2147483647 ∧ 2078456333 < 2147483647) ∧ (856402910 < 2147483647 ∧ 1203290467 < 2147483647); omega) canonical13 (by rfl)
#print axioms add13
theorem mul12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1184276229#u32 853882849#u32 1036962464#u32 395885796#u32) (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32)=ok (q 1473295188#u32 371513894#u32 623318889#u32 118581495#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1184276229 < 2147483647 ∧ 853882849 < 2147483647) ∧ (1036962464 < 2147483647 ∧ 395885796 < 2147483647); omega) (by change (810819047 < 2147483647 ∧ 1156380883 < 2147483647) ∧ (768810467 < 2147483647 ∧ 1018558903 < 2147483647); omega) (by rfl)
#print axioms mul12
theorem add12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1473295188#u32 371513894#u32 623318889#u32 118581495#u32) c12=ok (q 1016692290#u32 1272591029#u32 1790157654#u32 370398977#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1473295188 < 2147483647 ∧ 371513894 < 2147483647) ∧ (623318889 < 2147483647 ∧ 118581495 < 2147483647); omega) canonical12 (by rfl)
#print axioms add12
theorem mul11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1016692290#u32 1272591029#u32 1790157654#u32 370398977#u32) (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32)=ok (q 2031325833#u32 823718590#u32 334033543#u32 896782681#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1016692290 < 2147483647 ∧ 1272591029 < 2147483647) ∧ (1790157654 < 2147483647 ∧ 370398977 < 2147483647); omega) (by change (810819047 < 2147483647 ∧ 1156380883 < 2147483647) ∧ (768810467 < 2147483647 ∧ 1018558903 < 2147483647); omega) (by rfl)
#print axioms mul11
theorem add11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2031325833#u32 823718590#u32 334033543#u32 896782681#u32) c11=ok (q 2042846581#u32 1704731788#u32 371545720#u32 1617632#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2031325833 < 2147483647 ∧ 823718590 < 2147483647) ∧ (334033543 < 2147483647 ∧ 896782681 < 2147483647); omega) canonical11 (by rfl)
#print axioms add11
theorem mul10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2042846581#u32 1704731788#u32 371545720#u32 1617632#u32) (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32)=ok (q 1812261528#u32 434547412#u32 1852534784#u32 1176167428#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2042846581 < 2147483647 ∧ 1704731788 < 2147483647) ∧ (371545720 < 2147483647 ∧ 1617632 < 2147483647); omega) (by change (810819047 < 2147483647 ∧ 1156380883 < 2147483647) ∧ (768810467 < 2147483647 ∧ 1018558903 < 2147483647); omega) (by rfl)
#print axioms mul10
theorem add10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1812261528#u32 434547412#u32 1852534784#u32 1176167428#u32) c10=ok (q 1391658378#u32 1662584040#u32 1953180455#u32 1051757755#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1812261528 < 2147483647 ∧ 434547412 < 2147483647) ∧ (1852534784 < 2147483647 ∧ 1176167428 < 2147483647); omega) canonical10 (by rfl)
#print axioms add10
theorem mul09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1391658378#u32 1662584040#u32 1953180455#u32 1051757755#u32) (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32)=ok (q 31442210#u32 1926107705#u32 1765216528#u32 1350847113#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1391658378 < 2147483647 ∧ 1662584040 < 2147483647) ∧ (1953180455 < 2147483647 ∧ 1051757755 < 2147483647); omega) (by change (810819047 < 2147483647 ∧ 1156380883 < 2147483647) ∧ (768810467 < 2147483647 ∧ 1018558903 < 2147483647); omega) (by rfl)
#print axioms mul09
theorem add09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 31442210#u32 1926107705#u32 1765216528#u32 1350847113#u32) c09=ok (q 514706045#u32 2059201939#u32 783025035#u32 1477340554#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (31442210 < 2147483647 ∧ 1926107705 < 2147483647) ∧ (1765216528 < 2147483647 ∧ 1350847113 < 2147483647); omega) canonical09 (by rfl)
#print axioms add09
theorem mul08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 514706045#u32 2059201939#u32 783025035#u32 1477340554#u32) (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32)=ok (q 1184649633#u32 1018696677#u32 704250227#u32 2065150670#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (514706045 < 2147483647 ∧ 2059201939 < 2147483647) ∧ (783025035 < 2147483647 ∧ 1477340554 < 2147483647); omega) (by change (810819047 < 2147483647 ∧ 1156380883 < 2147483647) ∧ (768810467 < 2147483647 ∧ 1018558903 < 2147483647); omega) (by rfl)
#print axioms mul08
theorem add08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1184649633#u32 1018696677#u32 704250227#u32 2065150670#u32) c08=ok (q 2048916599#u32 1279448734#u32 1014457001#u32 341648023#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1184649633 < 2147483647 ∧ 1018696677 < 2147483647) ∧ (704250227 < 2147483647 ∧ 2065150670 < 2147483647); omega) canonical08 (by rfl)
#print axioms add08
theorem mul07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2048916599#u32 1279448734#u32 1014457001#u32 341648023#u32) (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32)=ok (q 2144941165#u32 158478731#u32 1444536450#u32 320821479#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2048916599 < 2147483647 ∧ 1279448734 < 2147483647) ∧ (1014457001 < 2147483647 ∧ 341648023 < 2147483647); omega) (by change (810819047 < 2147483647 ∧ 1156380883 < 2147483647) ∧ (768810467 < 2147483647 ∧ 1018558903 < 2147483647); omega) (by rfl)
#print axioms mul07
theorem add07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2144941165#u32 158478731#u32 1444536450#u32 320821479#u32) c07=ok (q 608174983#u32 1804903868#u32 1858884194#u32 344235399#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2144941165 < 2147483647 ∧ 158478731 < 2147483647) ∧ (1444536450 < 2147483647 ∧ 320821479 < 2147483647); omega) canonical07 (by rfl)
#print axioms add07
theorem mul06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 608174983#u32 1804903868#u32 1858884194#u32 344235399#u32) (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32)=ok (q 507409271#u32 390494012#u32 1481085624#u32 1923644640#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (608174983 < 2147483647 ∧ 1804903868 < 2147483647) ∧ (1858884194 < 2147483647 ∧ 344235399 < 2147483647); omega) (by change (810819047 < 2147483647 ∧ 1156380883 < 2147483647) ∧ (768810467 < 2147483647 ∧ 1018558903 < 2147483647); omega) (by rfl)
#print axioms mul06
theorem add06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 507409271#u32 390494012#u32 1481085624#u32 1923644640#u32) c06=ok (q 621211103#u32 2009376722#u32 1005985245#u32 427250115#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (507409271 < 2147483647 ∧ 390494012 < 2147483647) ∧ (1481085624 < 2147483647 ∧ 1923644640 < 2147483647); omega) canonical06 (by rfl)
#print axioms add06
theorem mul05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 621211103#u32 2009376722#u32 1005985245#u32 427250115#u32) (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32)=ok (q 536136138#u32 937531642#u32 1906629987#u32 1010625414#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (621211103 < 2147483647 ∧ 2009376722 < 2147483647) ∧ (1005985245 < 2147483647 ∧ 427250115 < 2147483647); omega) (by change (810819047 < 2147483647 ∧ 1156380883 < 2147483647) ∧ (768810467 < 2147483647 ∧ 1018558903 < 2147483647); omega) (by rfl)
#print axioms mul05
theorem add05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 536136138#u32 937531642#u32 1906629987#u32 1010625414#u32) c05=ok (q 1597886573#u32 259281020#u32 2095232500#u32 174417716#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (536136138 < 2147483647 ∧ 937531642 < 2147483647) ∧ (1906629987 < 2147483647 ∧ 1010625414 < 2147483647); omega) canonical05 (by rfl)
#print axioms add05
theorem mul04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1597886573#u32 259281020#u32 2095232500#u32 174417716#u32) (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32)=ok (q 2104748270#u32 1058263425#u32 389788562#u32 849546385#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1597886573 < 2147483647 ∧ 259281020 < 2147483647) ∧ (2095232500 < 2147483647 ∧ 174417716 < 2147483647); omega) (by change (810819047 < 2147483647 ∧ 1156380883 < 2147483647) ∧ (768810467 < 2147483647 ∧ 1018558903 < 2147483647); omega) (by rfl)
#print axioms mul04
theorem add04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2104748270#u32 1058263425#u32 389788562#u32 849546385#u32) c04=ok (q 1366309174#u32 1447624410#u32 1378671649#u32 1430690594#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2104748270 < 2147483647 ∧ 1058263425 < 2147483647) ∧ (389788562 < 2147483647 ∧ 849546385 < 2147483647); omega) canonical04 (by rfl)
#print axioms add04
theorem mul03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1366309174#u32 1447624410#u32 1378671649#u32 1430690594#u32) (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32)=ok (q 377111568#u32 642968334#u32 1829734073#u32 1331703315#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1366309174 < 2147483647 ∧ 1447624410 < 2147483647) ∧ (1378671649 < 2147483647 ∧ 1430690594 < 2147483647); omega) (by change (810819047 < 2147483647 ∧ 1156380883 < 2147483647) ∧ (768810467 < 2147483647 ∧ 1018558903 < 2147483647); omega) (by rfl)
#print axioms mul03
theorem add03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 377111568#u32 642968334#u32 1829734073#u32 1331703315#u32) c03=ok (q 1576744314#u32 783406237#u32 516931736#u32 1190481310#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (377111568 < 2147483647 ∧ 642968334 < 2147483647) ∧ (1829734073 < 2147483647 ∧ 1331703315 < 2147483647); omega) canonical03 (by rfl)
#print axioms add03
theorem mul02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1576744314#u32 783406237#u32 516931736#u32 1190481310#u32) (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32)=ok (q 1060944342#u32 1182397091#u32 746361039#u32 899485601#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1576744314 < 2147483647 ∧ 783406237 < 2147483647) ∧ (516931736 < 2147483647 ∧ 1190481310 < 2147483647); omega) (by change (810819047 < 2147483647 ∧ 1156380883 < 2147483647) ∧ (768810467 < 2147483647 ∧ 1018558903 < 2147483647); omega) (by rfl)
#print axioms mul02
theorem add02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1060944342#u32 1182397091#u32 746361039#u32 899485601#u32) c02=ok (q 975948820#u32 1376821780#u32 1529019573#u32 457272563#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1060944342 < 2147483647 ∧ 1182397091 < 2147483647) ∧ (746361039 < 2147483647 ∧ 899485601 < 2147483647); omega) canonical02 (by rfl)
#print axioms add02
theorem mul01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 975948820#u32 1376821780#u32 1529019573#u32 457272563#u32) (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32)=ok (q 979479723#u32 1833322415#u32 1602218222#u32 1031731765#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (975948820 < 2147483647 ∧ 1376821780 < 2147483647) ∧ (1529019573 < 2147483647 ∧ 457272563 < 2147483647); omega) (by change (810819047 < 2147483647 ∧ 1156380883 < 2147483647) ∧ (768810467 < 2147483647 ∧ 1018558903 < 2147483647); omega) (by rfl)
#print axioms mul01
theorem add01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 979479723#u32 1833322415#u32 1602218222#u32 1031731765#u32) c01=ok (q 2016697954#u32 701780070#u32 256697865#u32 42020006#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (979479723 < 2147483647 ∧ 1833322415 < 2147483647) ∧ (1602218222 < 2147483647 ∧ 1031731765 < 2147483647); omega) canonical01 (by rfl)
#print axioms add01
theorem mul00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2016697954#u32 701780070#u32 256697865#u32 42020006#u32) (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32)=ok (q 1091188365#u32 1002303490#u32 924149220#u32 1925210715#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2016697954 < 2147483647 ∧ 701780070 < 2147483647) ∧ (256697865 < 2147483647 ∧ 42020006 < 2147483647); omega) (by change (810819047 < 2147483647 ∧ 1156380883 < 2147483647) ∧ (768810467 < 2147483647 ∧ 1018558903 < 2147483647); omega) (by rfl)
#print axioms mul00
theorem add00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1091188365#u32 1002303490#u32 924149220#u32 1925210715#u32) c00=ok (q 372273128#u32 331300430#u32 427853818#u32 1780779409#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1091188365 < 2147483647 ∧ 1002303490 < 2147483647) ∧ (924149220 < 2147483647 ∧ 1925210715 < 2147483647); omega) canonical00 (by rfl)
#print axioms add00
def final : Q := (q 372273128#u32 331300430#u32 427853818#u32 1780779409#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 5#usize 14#usize initial 0#usize final := by
  refine .step (by change 14>0; omega) (JFr_IndexArithmetic.sub 14#usize 13#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32) from rfl) mul13 (show Array.index_usize p 13#usize=ok c13 from rfl) add13 ?_
  refine .step (by change 13>0; omega) (JFr_IndexArithmetic.sub 13#usize 12#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32) from rfl) mul12 (show Array.index_usize p 12#usize=ok c12 from rfl) add12 ?_
  refine .step (by change 12>0; omega) (JFr_IndexArithmetic.sub 12#usize 11#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32) from rfl) mul11 (show Array.index_usize p 11#usize=ok c11 from rfl) add11 ?_
  refine .step (by change 11>0; omega) (JFr_IndexArithmetic.sub 11#usize 10#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32) from rfl) mul10 (show Array.index_usize p 10#usize=ok c10 from rfl) add10 ?_
  refine .step (by change 10>0; omega) (JFr_IndexArithmetic.sub 10#usize 9#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32) from rfl) mul09 (show Array.index_usize p 9#usize=ok c09 from rfl) add09 ?_
  refine .step (by change 9>0; omega) (JFr_IndexArithmetic.sub 9#usize 8#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32) from rfl) mul08 (show Array.index_usize p 8#usize=ok c08 from rfl) add08 ?_
  refine .step (by change 8>0; omega) (JFr_IndexArithmetic.sub 8#usize 7#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32) from rfl) mul07 (show Array.index_usize p 7#usize=ok c07 from rfl) add07 ?_
  refine .step (by change 7>0; omega) (JFr_IndexArithmetic.sub 7#usize 6#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32) from rfl) mul06 (show Array.index_usize p 6#usize=ok c06 from rfl) add06 ?_
  refine .step (by change 6>0; omega) (JFr_IndexArithmetic.sub 6#usize 5#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32) from rfl) mul05 (show Array.index_usize p 5#usize=ok c05 from rfl) add05 ?_
  refine .step (by change 5>0; omega) (JFr_IndexArithmetic.sub 5#usize 4#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32) from rfl) mul04 (show Array.index_usize p 4#usize=ok c04 from rfl) add04 ?_
  refine .step (by change 4>0; omega) (JFr_IndexArithmetic.sub 4#usize 3#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32) from rfl) mul03 (show Array.index_usize p 3#usize=ok c03 from rfl) add03 ?_
  refine .step (by change 3>0; omega) (JFr_IndexArithmetic.sub 3#usize 2#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32) from rfl) mul02 (show Array.index_usize p 2#usize=ok c02 from rfl) add02 ?_
  refine .step (by change 2>0; omega) (JFr_IndexArithmetic.sub 2#usize 1#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32) from rfl) mul01 (show Array.index_usize p 1#usize=ok c01 from rfl) add01 ?_
  refine .step (by change 1>0; omega) (JFr_IndexArithmetic.sub 1#usize 0#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32) from rfl) mul00 (show Array.index_usize p 0#usize=ok c00 from rfl) add00 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner05_1
