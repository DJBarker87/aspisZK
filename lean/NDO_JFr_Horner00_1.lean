import NDO_JFr_Data00
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner00_1
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data00
def initial : Q := (q 812910159#u32 714244792#u32 348845800#u32 1897507794#u32)
theorem mul13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 812910159#u32 714244792#u32 348845800#u32 1897507794#u32) (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32)=ok (q 1748000505#u32 789543422#u32 1341006878#u32 825646529#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (812910159 < 2147483647 ∧ 714244792 < 2147483647) ∧ (348845800 < 2147483647 ∧ 1897507794 < 2147483647); omega) (by change (705343446 < 2147483647 ∧ 1948609717 < 2147483647) ∧ (871005084 < 2147483647 ∧ 203308705 < 2147483647); omega) (by rfl)
#print axioms mul13
theorem add13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1748000505#u32 789543422#u32 1341006878#u32 825646529#u32) c13=ok (q 942529472#u32 1691194713#u32 122141536#u32 2058233532#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1748000505 < 2147483647 ∧ 789543422 < 2147483647) ∧ (1341006878 < 2147483647 ∧ 825646529 < 2147483647); omega) canonical13 (by rfl)
#print axioms add13
theorem mul12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 942529472#u32 1691194713#u32 122141536#u32 2058233532#u32) (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32)=ok (q 1976841247#u32 1154555579#u32 1486604529#u32 1930953755#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (942529472 < 2147483647 ∧ 1691194713 < 2147483647) ∧ (122141536 < 2147483647 ∧ 2058233532 < 2147483647); omega) (by change (705343446 < 2147483647 ∧ 1948609717 < 2147483647) ∧ (871005084 < 2147483647 ∧ 203308705 < 2147483647); omega) (by rfl)
#print axioms mul12
theorem add12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1976841247#u32 1154555579#u32 1486604529#u32 1930953755#u32) c12=ok (q 1193096628#u32 1205850105#u32 812251014#u32 1666441695#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1976841247 < 2147483647 ∧ 1154555579 < 2147483647) ∧ (1486604529 < 2147483647 ∧ 1930953755 < 2147483647); omega) canonical12 (by rfl)
#print axioms add12
theorem mul11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1193096628#u32 1205850105#u32 812251014#u32 1666441695#u32) (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32)=ok (q 1542608328#u32 458931142#u32 1792380029#u32 935652194#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1193096628 < 2147483647 ∧ 1205850105 < 2147483647) ∧ (812251014 < 2147483647 ∧ 1666441695 < 2147483647); omega) (by change (705343446 < 2147483647 ∧ 1948609717 < 2147483647) ∧ (871005084 < 2147483647 ∧ 203308705 < 2147483647); omega) (by rfl)
#print axioms mul11
theorem add11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1542608328#u32 458931142#u32 1792380029#u32 935652194#u32) c11=ok (q 2142311578#u32 1181842057#u32 316396053#u32 1428252708#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1542608328 < 2147483647 ∧ 458931142 < 2147483647) ∧ (1792380029 < 2147483647 ∧ 935652194 < 2147483647); omega) canonical11 (by rfl)
#print axioms add11
theorem mul10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2142311578#u32 1181842057#u32 316396053#u32 1428252708#u32) (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32)=ok (q 1168877877#u32 331475192#u32 1173958440#u32 1425973802#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2142311578 < 2147483647 ∧ 1181842057 < 2147483647) ∧ (316396053 < 2147483647 ∧ 1428252708 < 2147483647); omega) (by change (705343446 < 2147483647 ∧ 1948609717 < 2147483647) ∧ (871005084 < 2147483647 ∧ 203308705 < 2147483647); omega) (by rfl)
#print axioms mul10
theorem add10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1168877877#u32 331475192#u32 1173958440#u32 1425973802#u32) c10=ok (q 2030246469#u32 187994516#u32 200815189#u32 379687977#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1168877877 < 2147483647 ∧ 331475192 < 2147483647) ∧ (1173958440 < 2147483647 ∧ 1425973802 < 2147483647); omega) canonical10 (by rfl)
#print axioms add10
theorem mul09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2030246469#u32 187994516#u32 200815189#u32 379687977#u32) (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32)=ok (q 641417750#u32 652081075#u32 1121886140#u32 1240011297#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2030246469 < 2147483647 ∧ 187994516 < 2147483647) ∧ (200815189 < 2147483647 ∧ 379687977 < 2147483647); omega) (by change (705343446 < 2147483647 ∧ 1948609717 < 2147483647) ∧ (871005084 < 2147483647 ∧ 203308705 < 2147483647); omega) (by rfl)
#print axioms mul09
theorem add09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 641417750#u32 652081075#u32 1121886140#u32 1240011297#u32) c09=ok (q 685137849#u32 2135766003#u32 1187285625#u32 665496222#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (641417750 < 2147483647 ∧ 652081075 < 2147483647) ∧ (1121886140 < 2147483647 ∧ 1240011297 < 2147483647); omega) canonical09 (by rfl)
#print axioms add09
theorem mul08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 685137849#u32 2135766003#u32 1187285625#u32 665496222#u32) (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32)=ok (q 1224590541#u32 1791698109#u32 1897130735#u32 1189270589#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (685137849 < 2147483647 ∧ 2135766003 < 2147483647) ∧ (1187285625 < 2147483647 ∧ 665496222 < 2147483647); omega) (by change (705343446 < 2147483647 ∧ 1948609717 < 2147483647) ∧ (871005084 < 2147483647 ∧ 203308705 < 2147483647); omega) (by rfl)
#print axioms mul08
theorem add08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1224590541#u32 1791698109#u32 1897130735#u32 1189270589#u32) c08=ok (q 909696993#u32 1277734168#u32 1144006511#u32 1732925047#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1224590541 < 2147483647 ∧ 1791698109 < 2147483647) ∧ (1897130735 < 2147483647 ∧ 1189270589 < 2147483647); omega) canonical08 (by rfl)
#print axioms add08
theorem mul07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 909696993#u32 1277734168#u32 1144006511#u32 1732925047#u32) (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32)=ok (q 1241531925#u32 1128616700#u32 1347844347#u32 900798579#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (909696993 < 2147483647 ∧ 1277734168 < 2147483647) ∧ (1144006511 < 2147483647 ∧ 1732925047 < 2147483647); omega) (by change (705343446 < 2147483647 ∧ 1948609717 < 2147483647) ∧ (871005084 < 2147483647 ∧ 203308705 < 2147483647); omega) (by rfl)
#print axioms mul07
theorem add07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1241531925#u32 1128616700#u32 1347844347#u32 900798579#u32) c07=ok (q 248534934#u32 1804912966#u32 601155587#u32 1357478138#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1241531925 < 2147483647 ∧ 1128616700 < 2147483647) ∧ (1347844347 < 2147483647 ∧ 900798579 < 2147483647); omega) canonical07 (by rfl)
#print axioms add07
theorem mul06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 248534934#u32 1804912966#u32 601155587#u32 1357478138#u32) (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32)=ok (q 1713857367#u32 200291983#u32 1430342393#u32 2009543883#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (248534934 < 2147483647 ∧ 1804912966 < 2147483647) ∧ (601155587 < 2147483647 ∧ 1357478138 < 2147483647); omega) (by change (705343446 < 2147483647 ∧ 1948609717 < 2147483647) ∧ (871005084 < 2147483647 ∧ 203308705 < 2147483647); omega) (by rfl)
#print axioms mul06
theorem add06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1713857367#u32 200291983#u32 1430342393#u32 2009543883#u32) c06=ok (q 902942747#u32 706186933#u32 103428281#u32 1051065516#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1713857367 < 2147483647 ∧ 200291983 < 2147483647) ∧ (1430342393 < 2147483647 ∧ 2009543883 < 2147483647); omega) canonical06 (by rfl)
#print axioms add06
theorem mul05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 902942747#u32 706186933#u32 103428281#u32 1051065516#u32) (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32)=ok (q 394132146#u32 1184771111#u32 636606003#u32 1837842425#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (902942747 < 2147483647 ∧ 706186933 < 2147483647) ∧ (103428281 < 2147483647 ∧ 1051065516 < 2147483647); omega) (by change (705343446 < 2147483647 ∧ 1948609717 < 2147483647) ∧ (871005084 < 2147483647 ∧ 203308705 < 2147483647); omega) (by rfl)
#print axioms mul05
theorem add05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 394132146#u32 1184771111#u32 636606003#u32 1837842425#u32) c05=ok (q 272111728#u32 619712408#u32 1695545294#u32 1302497148#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (394132146 < 2147483647 ∧ 1184771111 < 2147483647) ∧ (636606003 < 2147483647 ∧ 1837842425 < 2147483647); omega) canonical05 (by rfl)
#print axioms add05
theorem mul04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 272111728#u32 619712408#u32 1695545294#u32 1302497148#u32) (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32)=ok (q 2132563686#u32 250348935#u32 761100039#u32 1269851727#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (272111728 < 2147483647 ∧ 619712408 < 2147483647) ∧ (1695545294 < 2147483647 ∧ 1302497148 < 2147483647); omega) (by change (705343446 < 2147483647 ∧ 1948609717 < 2147483647) ∧ (871005084 < 2147483647 ∧ 203308705 < 2147483647); omega) (by rfl)
#print axioms mul04
theorem add04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2132563686#u32 250348935#u32 761100039#u32 1269851727#u32) c04=ok (q 466949195#u32 611944656#u32 669655789#u32 1740324131#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2132563686 < 2147483647 ∧ 250348935 < 2147483647) ∧ (761100039 < 2147483647 ∧ 1269851727 < 2147483647); omega) canonical04 (by rfl)
#print axioms add04
theorem mul03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 466949195#u32 611944656#u32 669655789#u32 1740324131#u32) (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32)=ok (q 1343021888#u32 871181139#u32 111556495#u32 999207305#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (466949195 < 2147483647 ∧ 611944656 < 2147483647) ∧ (669655789 < 2147483647 ∧ 1740324131 < 2147483647); omega) (by change (705343446 < 2147483647 ∧ 1948609717 < 2147483647) ∧ (871005084 < 2147483647 ∧ 203308705 < 2147483647); omega) (by rfl)
#print axioms mul03
theorem add03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1343021888#u32 871181139#u32 111556495#u32 999207305#u32) c03=ok (q 623052278#u32 1710389242#u32 1426585361#u32 453323903#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1343021888 < 2147483647 ∧ 871181139 < 2147483647) ∧ (111556495 < 2147483647 ∧ 999207305 < 2147483647); omega) canonical03 (by rfl)
#print axioms add03
theorem mul02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 623052278#u32 1710389242#u32 1426585361#u32 453323903#u32) (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32)=ok (q 1144912433#u32 780663125#u32 142162723#u32 1126293821#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (623052278 < 2147483647 ∧ 1710389242 < 2147483647) ∧ (1426585361 < 2147483647 ∧ 453323903 < 2147483647); omega) (by change (705343446 < 2147483647 ∧ 1948609717 < 2147483647) ∧ (871005084 < 2147483647 ∧ 203308705 < 2147483647); omega) (by rfl)
#print axioms mul02
theorem add02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1144912433#u32 780663125#u32 142162723#u32 1126293821#u32) c02=ok (q 242219653#u32 1301763875#u32 1338637012#u32 87757559#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1144912433 < 2147483647 ∧ 780663125 < 2147483647) ∧ (142162723 < 2147483647 ∧ 1126293821 < 2147483647); omega) canonical02 (by rfl)
#print axioms add02
theorem mul01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 242219653#u32 1301763875#u32 1338637012#u32 87757559#u32) (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32)=ok (q 125861649#u32 402989451#u32 1843507063#u32 1224389616#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (242219653 < 2147483647 ∧ 1301763875 < 2147483647) ∧ (1338637012 < 2147483647 ∧ 87757559 < 2147483647); omega) (by change (705343446 < 2147483647 ∧ 1948609717 < 2147483647) ∧ (871005084 < 2147483647 ∧ 203308705 < 2147483647); omega) (by rfl)
#print axioms mul01
theorem add01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 125861649#u32 402989451#u32 1843507063#u32 1224389616#u32) c01=ok (q 1250574709#u32 726334343#u32 1737826289#u32 1809489884#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (125861649 < 2147483647 ∧ 402989451 < 2147483647) ∧ (1843507063 < 2147483647 ∧ 1224389616 < 2147483647); omega) canonical01 (by rfl)
#print axioms add01
theorem mul00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1250574709#u32 726334343#u32 1737826289#u32 1809489884#u32) (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32)=ok (q 346385822#u32 2033880182#u32 807608202#u32 1071372540#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1250574709 < 2147483647 ∧ 726334343 < 2147483647) ∧ (1737826289 < 2147483647 ∧ 1809489884 < 2147483647); omega) (by change (705343446 < 2147483647 ∧ 1948609717 < 2147483647) ∧ (871005084 < 2147483647 ∧ 203308705 < 2147483647); omega) (by rfl)
#print axioms mul00
theorem add00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 346385822#u32 2033880182#u32 807608202#u32 1071372540#u32) c00=ok (q 1043776513#u32 1161764315#u32 2088723454#u32 1016233752#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (346385822 < 2147483647 ∧ 2033880182 < 2147483647) ∧ (807608202 < 2147483647 ∧ 1071372540 < 2147483647); omega) canonical00 (by rfl)
#print axioms add00
def final : Q := (q 1043776513#u32 1161764315#u32 2088723454#u32 1016233752#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 0#usize 14#usize initial 0#usize final := by
  refine .step (by change 14>0; omega) (JFr_IndexArithmetic.sub 14#usize 13#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32) from rfl) mul13 (show Array.index_usize p 13#usize=ok c13 from rfl) add13 ?_
  refine .step (by change 13>0; omega) (JFr_IndexArithmetic.sub 13#usize 12#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32) from rfl) mul12 (show Array.index_usize p 12#usize=ok c12 from rfl) add12 ?_
  refine .step (by change 12>0; omega) (JFr_IndexArithmetic.sub 12#usize 11#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32) from rfl) mul11 (show Array.index_usize p 11#usize=ok c11 from rfl) add11 ?_
  refine .step (by change 11>0; omega) (JFr_IndexArithmetic.sub 11#usize 10#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32) from rfl) mul10 (show Array.index_usize p 10#usize=ok c10 from rfl) add10 ?_
  refine .step (by change 10>0; omega) (JFr_IndexArithmetic.sub 10#usize 9#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32) from rfl) mul09 (show Array.index_usize p 9#usize=ok c09 from rfl) add09 ?_
  refine .step (by change 9>0; omega) (JFr_IndexArithmetic.sub 9#usize 8#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32) from rfl) mul08 (show Array.index_usize p 8#usize=ok c08 from rfl) add08 ?_
  refine .step (by change 8>0; omega) (JFr_IndexArithmetic.sub 8#usize 7#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32) from rfl) mul07 (show Array.index_usize p 7#usize=ok c07 from rfl) add07 ?_
  refine .step (by change 7>0; omega) (JFr_IndexArithmetic.sub 7#usize 6#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32) from rfl) mul06 (show Array.index_usize p 6#usize=ok c06 from rfl) add06 ?_
  refine .step (by change 6>0; omega) (JFr_IndexArithmetic.sub 6#usize 5#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32) from rfl) mul05 (show Array.index_usize p 5#usize=ok c05 from rfl) add05 ?_
  refine .step (by change 5>0; omega) (JFr_IndexArithmetic.sub 5#usize 4#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32) from rfl) mul04 (show Array.index_usize p 4#usize=ok c04 from rfl) add04 ?_
  refine .step (by change 4>0; omega) (JFr_IndexArithmetic.sub 4#usize 3#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32) from rfl) mul03 (show Array.index_usize p 3#usize=ok c03 from rfl) add03 ?_
  refine .step (by change 3>0; omega) (JFr_IndexArithmetic.sub 3#usize 2#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32) from rfl) mul02 (show Array.index_usize p 2#usize=ok c02 from rfl) add02 ?_
  refine .step (by change 2>0; omega) (JFr_IndexArithmetic.sub 2#usize 1#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32) from rfl) mul01 (show Array.index_usize p 1#usize=ok c01 from rfl) add01 ?_
  refine .step (by change 1>0; omega) (JFr_IndexArithmetic.sub 1#usize 0#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32) from rfl) mul00 (show Array.index_usize p 0#usize=ok c00 from rfl) add00 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner00_1
