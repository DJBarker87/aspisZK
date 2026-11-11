import NDO_JFr_Data05
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner05_1
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data05
def initial : Q := (q 1259000379#u32 1972168632#u32 520012117#u32 457902977#u32)
theorem mul13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1259000379#u32 1972168632#u32 520012117#u32 457902977#u32) (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32)=ok (q 1958733438#u32 2139171527#u32 939102616#u32 1526770051#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1259000379 < 2147483647 ∧ 1972168632 < 2147483647) ∧ (520012117 < 2147483647 ∧ 457902977 < 2147483647); omega) (by change (1976533199 < 2147483647 ∧ 2142788478 < 2147483647) ∧ (1835806328 < 2147483647 ∧ 1950703221 < 2147483647); omega) (by rfl)
#print axioms mul13
theorem add13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1958733438#u32 2139171527#u32 939102616#u32 1526770051#u32) c13=ok (q 1648380123#u32 2067915111#u32 1098969562#u32 941378936#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1958733438 < 2147483647 ∧ 2139171527 < 2147483647) ∧ (939102616 < 2147483647 ∧ 1526770051 < 2147483647); omega) canonical13 (by rfl)
#print axioms add13
theorem mul12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1648380123#u32 2067915111#u32 1098969562#u32 941378936#u32) (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32)=ok (q 1475085885#u32 459777249#u32 1242423259#u32 946073691#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1648380123 < 2147483647 ∧ 2067915111 < 2147483647) ∧ (1098969562 < 2147483647 ∧ 941378936 < 2147483647); omega) (by change (1976533199 < 2147483647 ∧ 2142788478 < 2147483647) ∧ (1835806328 < 2147483647 ∧ 1950703221 < 2147483647); omega) (by rfl)
#print axioms mul12
theorem add12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1475085885#u32 459777249#u32 1242423259#u32 946073691#u32) c12=ok (q 1165270294#u32 1186603148#u32 16581952#u32 1593754590#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1475085885 < 2147483647 ∧ 459777249 < 2147483647) ∧ (1242423259 < 2147483647 ∧ 946073691 < 2147483647); omega) canonical12 (by rfl)
#print axioms add12
theorem mul11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1165270294#u32 1186603148#u32 16581952#u32 1593754590#u32) (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32)=ok (q 265088751#u32 1538863328#u32 1980662700#u32 518057439#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1165270294 < 2147483647 ∧ 1186603148 < 2147483647) ∧ (16581952 < 2147483647 ∧ 1593754590 < 2147483647); omega) (by change (1976533199 < 2147483647 ∧ 2142788478 < 2147483647) ∧ (1835806328 < 2147483647 ∧ 1950703221 < 2147483647); omega) (by rfl)
#print axioms mul11
theorem add11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 265088751#u32 1538863328#u32 1980662700#u32 518057439#u32) c11=ok (q 605014846#u32 1915497493#u32 1494421095#u32 1488572031#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (265088751 < 2147483647 ∧ 1538863328 < 2147483647) ∧ (1980662700 < 2147483647 ∧ 518057439 < 2147483647); omega) canonical11 (by rfl)
#print axioms add11
theorem mul10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 605014846#u32 1915497493#u32 1494421095#u32 1488572031#u32) (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32)=ok (q 437754970#u32 394928485#u32 1751096559#u32 212343557#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (605014846 < 2147483647 ∧ 1915497493 < 2147483647) ∧ (1494421095 < 2147483647 ∧ 1488572031 < 2147483647); omega) (by change (1976533199 < 2147483647 ∧ 2142788478 < 2147483647) ∧ (1835806328 < 2147483647 ∧ 1950703221 < 2147483647); omega) (by rfl)
#print axioms mul10
theorem add10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 437754970#u32 394928485#u32 1751096559#u32 212343557#u32) c10=ok (q 235224342#u32 2037418397#u32 1255177157#u32 1699348047#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (437754970 < 2147483647 ∧ 394928485 < 2147483647) ∧ (1751096559 < 2147483647 ∧ 212343557 < 2147483647); omega) canonical10 (by rfl)
#print axioms add10
theorem mul09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 235224342#u32 2037418397#u32 1255177157#u32 1699348047#u32) (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32)=ok (q 706897261#u32 525506489#u32 1309568765#u32 787877189#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (235224342 < 2147483647 ∧ 2037418397 < 2147483647) ∧ (1255177157 < 2147483647 ∧ 1699348047 < 2147483647); omega) (by change (1976533199 < 2147483647 ∧ 2142788478 < 2147483647) ∧ (1835806328 < 2147483647 ∧ 1950703221 < 2147483647); omega) (by rfl)
#print axioms mul09
theorem add09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 706897261#u32 525506489#u32 1309568765#u32 787877189#u32) c09=ok (q 1264229313#u32 737427147#u32 302816373#u32 28143702#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (706897261 < 2147483647 ∧ 525506489 < 2147483647) ∧ (1309568765 < 2147483647 ∧ 787877189 < 2147483647); omega) canonical09 (by rfl)
#print axioms add09
theorem mul08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1264229313#u32 737427147#u32 302816373#u32 28143702#u32) (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32)=ok (q 1729790619#u32 1084531056#u32 1976930559#u32 544882361#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1264229313 < 2147483647 ∧ 737427147 < 2147483647) ∧ (302816373 < 2147483647 ∧ 28143702 < 2147483647); omega) (by change (1976533199 < 2147483647 ∧ 2142788478 < 2147483647) ∧ (1835806328 < 2147483647 ∧ 1950703221 < 2147483647); omega) (by rfl)
#print axioms mul08
theorem add08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1729790619#u32 1084531056#u32 1976930559#u32 544882361#u32) c08=ok (q 224162775#u32 560269817#u32 1291072166#u32 1380789052#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1729790619 < 2147483647 ∧ 1084531056 < 2147483647) ∧ (1976930559 < 2147483647 ∧ 544882361 < 2147483647); omega) canonical08 (by rfl)
#print axioms add08
theorem mul07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 224162775#u32 560269817#u32 1291072166#u32 1380789052#u32) (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32)=ok (q 812292344#u32 277385193#u32 674923014#u32 1882362669#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (224162775 < 2147483647 ∧ 560269817 < 2147483647) ∧ (1291072166 < 2147483647 ∧ 1380789052 < 2147483647); omega) (by change (1976533199 < 2147483647 ∧ 2142788478 < 2147483647) ∧ (1835806328 < 2147483647 ∧ 1950703221 < 2147483647); omega) (by rfl)
#print axioms mul07
theorem add07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 812292344#u32 277385193#u32 674923014#u32 1882362669#u32) c07=ok (q 1092192815#u32 913180950#u32 1864548629#u32 633751057#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (812292344 < 2147483647 ∧ 277385193 < 2147483647) ∧ (674923014 < 2147483647 ∧ 1882362669 < 2147483647); omega) canonical07 (by rfl)
#print axioms add07
theorem mul06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1092192815#u32 913180950#u32 1864548629#u32 633751057#u32) (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32)=ok (q 737979150#u32 2067271719#u32 382365625#u32 2127916526#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1092192815 < 2147483647 ∧ 913180950 < 2147483647) ∧ (1864548629 < 2147483647 ∧ 633751057 < 2147483647); omega) (by change (1976533199 < 2147483647 ∧ 2142788478 < 2147483647) ∧ (1835806328 < 2147483647 ∧ 1950703221 < 2147483647); omega) (by rfl)
#print axioms mul06
theorem add06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 737979150#u32 2067271719#u32 382365625#u32 2127916526#u32) c06=ok (q 1502510908#u32 468375985#u32 193970488#u32 751171449#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (737979150 < 2147483647 ∧ 2067271719 < 2147483647) ∧ (382365625 < 2147483647 ∧ 2127916526 < 2147483647); omega) canonical06 (by rfl)
#print axioms add06
theorem mul05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1502510908#u32 468375985#u32 193970488#u32 751171449#u32) (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32)=ok (q 417246758#u32 34442371#u32 1089121068#u32 1630582708#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1502510908 < 2147483647 ∧ 468375985 < 2147483647) ∧ (193970488 < 2147483647 ∧ 751171449 < 2147483647); omega) (by change (1976533199 < 2147483647 ∧ 2142788478 < 2147483647) ∧ (1835806328 < 2147483647 ∧ 1950703221 < 2147483647); omega) (by rfl)
#print axioms mul05
theorem add05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 417246758#u32 34442371#u32 1089121068#u32 1630582708#u32) c05=ok (q 2099090290#u32 1550293733#u32 1187714487#u32 304584786#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (417246758 < 2147483647 ∧ 34442371 < 2147483647) ∧ (1089121068 < 2147483647 ∧ 1630582708 < 2147483647); omega) canonical05 (by rfl)
#print axioms add05
theorem mul04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2099090290#u32 1550293733#u32 1187714487#u32 304584786#u32) (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32)=ok (q 319789893#u32 1599126291#u32 628072#u32 1544678451#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2099090290 < 2147483647 ∧ 1550293733 < 2147483647) ∧ (1187714487 < 2147483647 ∧ 304584786 < 2147483647); omega) (by change (1976533199 < 2147483647 ∧ 2142788478 < 2147483647) ∧ (1835806328 < 2147483647 ∧ 1950703221 < 2147483647); omega) (by rfl)
#print axioms mul04
theorem add04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 319789893#u32 1599126291#u32 628072#u32 1544678451#u32) c04=ok (q 1592460435#u32 86731785#u32 661678180#u32 202334354#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (319789893 < 2147483647 ∧ 1599126291 < 2147483647) ∧ (628072 < 2147483647 ∧ 1544678451 < 2147483647); omega) canonical04 (by rfl)
#print axioms add04
theorem mul03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1592460435#u32 86731785#u32 661678180#u32 202334354#u32) (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32)=ok (q 927990493#u32 1162345624#u32 417537451#u32 2004028594#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1592460435 < 2147483647 ∧ 86731785 < 2147483647) ∧ (661678180 < 2147483647 ∧ 202334354 < 2147483647); omega) (by change (1976533199 < 2147483647 ∧ 2142788478 < 2147483647) ∧ (1835806328 < 2147483647 ∧ 1950703221 < 2147483647); omega) (by rfl)
#print axioms mul03
theorem add03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 927990493#u32 1162345624#u32 417537451#u32 2004028594#u32) c03=ok (q 1251181952#u32 441422058#u32 1060106532#u32 43570031#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (927990493 < 2147483647 ∧ 1162345624 < 2147483647) ∧ (417537451 < 2147483647 ∧ 2004028594 < 2147483647); omega) canonical03 (by rfl)
#print axioms add03
theorem mul02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1251181952#u32 441422058#u32 1060106532#u32 43570031#u32) (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32)=ok (q 1515369861#u32 1684603003#u32 825429846#u32 1156023208#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1251181952 < 2147483647 ∧ 441422058 < 2147483647) ∧ (1060106532 < 2147483647 ∧ 43570031 < 2147483647); omega) (by change (1976533199 < 2147483647 ∧ 2142788478 < 2147483647) ∧ (1835806328 < 2147483647 ∧ 1950703221 < 2147483647); omega) (by rfl)
#print axioms mul02
theorem add02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1515369861#u32 1684603003#u32 825429846#u32 1156023208#u32) c02=ok (q 408562067#u32 34848836#u32 37144045#u32 1291352189#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1515369861 < 2147483647 ∧ 1684603003 < 2147483647) ∧ (825429846 < 2147483647 ∧ 1156023208 < 2147483647); omega) canonical02 (by rfl)
#print axioms add02
theorem mul01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 408562067#u32 34848836#u32 37144045#u32 1291352189#u32) (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32)=ok (q 1142801055#u32 1515386173#u32 1742895057#u32 1886179914#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (408562067 < 2147483647 ∧ 34848836 < 2147483647) ∧ (37144045 < 2147483647 ∧ 1291352189 < 2147483647); omega) (by change (1976533199 < 2147483647 ∧ 2142788478 < 2147483647) ∧ (1835806328 < 2147483647 ∧ 1950703221 < 2147483647); omega) (by rfl)
#print axioms mul01
theorem add01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1142801055#u32 1515386173#u32 1742895057#u32 1886179914#u32) c01=ok (q 312359087#u32 1220940601#u32 807135846#u32 13770031#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1142801055 < 2147483647 ∧ 1515386173 < 2147483647) ∧ (1742895057 < 2147483647 ∧ 1886179914 < 2147483647); omega) canonical01 (by rfl)
#print axioms add01
theorem mul00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 312359087#u32 1220940601#u32 807135846#u32 13770031#u32) (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32)=ok (q 1612889156#u32 721390617#u32 774775855#u32 1029975194#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (312359087 < 2147483647 ∧ 1220940601 < 2147483647) ∧ (807135846 < 2147483647 ∧ 13770031 < 2147483647); omega) (by change (1976533199 < 2147483647 ∧ 2142788478 < 2147483647) ∧ (1835806328 < 2147483647 ∧ 1950703221 < 2147483647); omega) (by rfl)
#print axioms mul00
theorem add00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1612889156#u32 721390617#u32 774775855#u32 1029975194#u32) c00=ok (q 703625559#u32 22844908#u32 1869120602#u32 703671562#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1612889156 < 2147483647 ∧ 721390617 < 2147483647) ∧ (774775855 < 2147483647 ∧ 1029975194 < 2147483647); omega) canonical00 (by rfl)
#print axioms add00
def final : Q := (q 703625559#u32 22844908#u32 1869120602#u32 703671562#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 5#usize 14#usize initial 0#usize final := by
  refine .step (by change 14>0; omega) (JFr_IndexArithmetic.sub 14#usize 13#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32) from rfl) mul13 (show Array.index_usize p 13#usize=ok c13 from rfl) add13 ?_
  refine .step (by change 13>0; omega) (JFr_IndexArithmetic.sub 13#usize 12#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32) from rfl) mul12 (show Array.index_usize p 12#usize=ok c12 from rfl) add12 ?_
  refine .step (by change 12>0; omega) (JFr_IndexArithmetic.sub 12#usize 11#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32) from rfl) mul11 (show Array.index_usize p 11#usize=ok c11 from rfl) add11 ?_
  refine .step (by change 11>0; omega) (JFr_IndexArithmetic.sub 11#usize 10#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32) from rfl) mul10 (show Array.index_usize p 10#usize=ok c10 from rfl) add10 ?_
  refine .step (by change 10>0; omega) (JFr_IndexArithmetic.sub 10#usize 9#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32) from rfl) mul09 (show Array.index_usize p 9#usize=ok c09 from rfl) add09 ?_
  refine .step (by change 9>0; omega) (JFr_IndexArithmetic.sub 9#usize 8#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32) from rfl) mul08 (show Array.index_usize p 8#usize=ok c08 from rfl) add08 ?_
  refine .step (by change 8>0; omega) (JFr_IndexArithmetic.sub 8#usize 7#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32) from rfl) mul07 (show Array.index_usize p 7#usize=ok c07 from rfl) add07 ?_
  refine .step (by change 7>0; omega) (JFr_IndexArithmetic.sub 7#usize 6#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32) from rfl) mul06 (show Array.index_usize p 6#usize=ok c06 from rfl) add06 ?_
  refine .step (by change 6>0; omega) (JFr_IndexArithmetic.sub 6#usize 5#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32) from rfl) mul05 (show Array.index_usize p 5#usize=ok c05 from rfl) add05 ?_
  refine .step (by change 5>0; omega) (JFr_IndexArithmetic.sub 5#usize 4#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32) from rfl) mul04 (show Array.index_usize p 4#usize=ok c04 from rfl) add04 ?_
  refine .step (by change 4>0; omega) (JFr_IndexArithmetic.sub 4#usize 3#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32) from rfl) mul03 (show Array.index_usize p 3#usize=ok c03 from rfl) add03 ?_
  refine .step (by change 3>0; omega) (JFr_IndexArithmetic.sub 3#usize 2#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32) from rfl) mul02 (show Array.index_usize p 2#usize=ok c02 from rfl) add02 ?_
  refine .step (by change 2>0; omega) (JFr_IndexArithmetic.sub 2#usize 1#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32) from rfl) mul01 (show Array.index_usize p 1#usize=ok c01 from rfl) add01 ?_
  refine .step (by change 1>0; omega) (JFr_IndexArithmetic.sub 1#usize 0#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32) from rfl) mul00 (show Array.index_usize p 0#usize=ok c00 from rfl) add00 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner05_1
