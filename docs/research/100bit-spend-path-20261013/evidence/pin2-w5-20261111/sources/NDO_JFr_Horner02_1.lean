import NDO_JFr_Data02
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner02_1
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data02
def initial : Q := (q 265808631#u32 1129757301#u32 1597192272#u32 66325017#u32)
theorem mul13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 265808631#u32 1129757301#u32 1597192272#u32 66325017#u32) (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32)=ok (q 1336419644#u32 595808530#u32 1425454302#u32 2037782901#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (265808631 < 2147483647 ∧ 1129757301 < 2147483647) ∧ (1597192272 < 2147483647 ∧ 66325017 < 2147483647); omega) (by change (1817229702 < 2147483647 ∧ 1607494202 < 2147483647) ∧ (2141385593 < 2147483647 ∧ 540773558 < 2147483647); omega) (by rfl)
#print axioms mul13
theorem add13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1336419644#u32 595808530#u32 1425454302#u32 2037782901#u32) c13=ok (q 215104693#u32 318774660#u32 1963813799#u32 1051297065#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1336419644 < 2147483647 ∧ 595808530 < 2147483647) ∧ (1425454302 < 2147483647 ∧ 2037782901 < 2147483647); omega) canonical13 (by rfl)
#print axioms add13
theorem mul12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 215104693#u32 318774660#u32 1963813799#u32 1051297065#u32) (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32)=ok (q 536831814#u32 1378526043#u32 1966051529#u32 1390489624#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (215104693 < 2147483647 ∧ 318774660 < 2147483647) ∧ (1963813799 < 2147483647 ∧ 1051297065 < 2147483647); omega) (by change (1817229702 < 2147483647 ∧ 1607494202 < 2147483647) ∧ (2141385593 < 2147483647 ∧ 540773558 < 2147483647); omega) (by rfl)
#print axioms mul12
theorem add12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 536831814#u32 1378526043#u32 1966051529#u32 1390489624#u32) c12=ok (q 1464957578#u32 1648631266#u32 1643978580#u32 1075027015#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (536831814 < 2147483647 ∧ 1378526043 < 2147483647) ∧ (1966051529 < 2147483647 ∧ 1390489624 < 2147483647); omega) canonical12 (by rfl)
#print axioms add12
theorem mul11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1464957578#u32 1648631266#u32 1643978580#u32 1075027015#u32) (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32)=ok (q 1146747966#u32 1261075361#u32 975182840#u32 1557349624#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1464957578 < 2147483647 ∧ 1648631266 < 2147483647) ∧ (1643978580 < 2147483647 ∧ 1075027015 < 2147483647); omega) (by change (1817229702 < 2147483647 ∧ 1607494202 < 2147483647) ∧ (2141385593 < 2147483647 ∧ 540773558 < 2147483647); omega) (by rfl)
#print axioms mul11
theorem add11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1146747966#u32 1261075361#u32 975182840#u32 1557349624#u32) c11=ok (q 671845927#u32 1598911905#u32 1049789449#u32 1095445546#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1146747966 < 2147483647 ∧ 1261075361 < 2147483647) ∧ (975182840 < 2147483647 ∧ 1557349624 < 2147483647); omega) canonical11 (by rfl)
#print axioms add11
theorem mul10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 671845927#u32 1598911905#u32 1049789449#u32 1095445546#u32) (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32)=ok (q 1526957544#u32 675867208#u32 990804397#u32 417192360#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (671845927 < 2147483647 ∧ 1598911905 < 2147483647) ∧ (1049789449 < 2147483647 ∧ 1095445546 < 2147483647); omega) (by change (1817229702 < 2147483647 ∧ 1607494202 < 2147483647) ∧ (2141385593 < 2147483647 ∧ 540773558 < 2147483647); omega) (by rfl)
#print axioms mul10
theorem add10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1526957544#u32 675867208#u32 990804397#u32 417192360#u32) c10=ok (q 1846168002#u32 1503456947#u32 256530412#u32 410313006#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1526957544 < 2147483647 ∧ 675867208 < 2147483647) ∧ (990804397 < 2147483647 ∧ 417192360 < 2147483647); omega) canonical10 (by rfl)
#print axioms add10
theorem mul09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1846168002#u32 1503456947#u32 256530412#u32 410313006#u32) (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32)=ok (q 1480310670#u32 818542310#u32 1697519871#u32 702590561#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1846168002 < 2147483647 ∧ 1503456947 < 2147483647) ∧ (256530412 < 2147483647 ∧ 410313006 < 2147483647); omega) (by change (1817229702 < 2147483647 ∧ 1607494202 < 2147483647) ∧ (2141385593 < 2147483647 ∧ 540773558 < 2147483647); omega) (by rfl)
#print axioms mul09
theorem add09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1480310670#u32 818542310#u32 1697519871#u32 702590561#u32) c09=ok (q 1539961234#u32 443040050#u32 1349377451#u32 1604241853#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1480310670 < 2147483647 ∧ 818542310 < 2147483647) ∧ (1697519871 < 2147483647 ∧ 702590561 < 2147483647); omega) canonical09 (by rfl)
#print axioms add09
theorem mul08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1539961234#u32 443040050#u32 1349377451#u32 1604241853#u32) (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32)=ok (q 2044749681#u32 380041162#u32 306607562#u32 944117811#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1539961234 < 2147483647 ∧ 443040050 < 2147483647) ∧ (1349377451 < 2147483647 ∧ 1604241853 < 2147483647); omega) (by change (1817229702 < 2147483647 ∧ 1607494202 < 2147483647) ∧ (2141385593 < 2147483647 ∧ 540773558 < 2147483647); omega) (by rfl)
#print axioms mul08
theorem add08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2044749681#u32 380041162#u32 306607562#u32 944117811#u32) c08=ok (q 1998873837#u32 651235551#u32 995117282#u32 1434211147#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2044749681 < 2147483647 ∧ 380041162 < 2147483647) ∧ (306607562 < 2147483647 ∧ 944117811 < 2147483647); omega) canonical08 (by rfl)
#print axioms add08
theorem mul07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1998873837#u32 651235551#u32 995117282#u32 1434211147#u32) (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32)=ok (q 1641854409#u32 963939828#u32 1336830004#u32 1472741421#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1998873837 < 2147483647 ∧ 651235551 < 2147483647) ∧ (995117282 < 2147483647 ∧ 1434211147 < 2147483647); omega) (by change (1817229702 < 2147483647 ∧ 1607494202 < 2147483647) ∧ (2141385593 < 2147483647 ∧ 540773558 < 2147483647); omega) (by rfl)
#print axioms mul07
theorem add07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1641854409#u32 963939828#u32 1336830004#u32 1472741421#u32) c07=ok (q 238053714#u32 781082661#u32 1207579808#u32 266680687#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1641854409 < 2147483647 ∧ 963939828 < 2147483647) ∧ (1336830004 < 2147483647 ∧ 1472741421 < 2147483647); omega) canonical07 (by rfl)
#print axioms add07
theorem mul06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 238053714#u32 781082661#u32 1207579808#u32 266680687#u32) (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32)=ok (q 403456957#u32 457903737#u32 32673989#u32 769477802#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (238053714 < 2147483647 ∧ 781082661 < 2147483647) ∧ (1207579808 < 2147483647 ∧ 266680687 < 2147483647); omega) (by change (1817229702 < 2147483647 ∧ 1607494202 < 2147483647) ∧ (2141385593 < 2147483647 ∧ 540773558 < 2147483647); omega) (by rfl)
#print axioms mul06
theorem add06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 403456957#u32 457903737#u32 32673989#u32 769477802#u32) c06=ok (q 1152897020#u32 1901938792#u32 94191942#u32 1480455591#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (403456957 < 2147483647 ∧ 457903737 < 2147483647) ∧ (32673989 < 2147483647 ∧ 769477802 < 2147483647); omega) canonical06 (by rfl)
#print axioms add06
theorem mul05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1152897020#u32 1901938792#u32 94191942#u32 1480455591#u32) (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32)=ok (q 1642986222#u32 855120263#u32 24802873#u32 1074150637#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1152897020 < 2147483647 ∧ 1901938792 < 2147483647) ∧ (94191942 < 2147483647 ∧ 1480455591 < 2147483647); omega) (by change (1817229702 < 2147483647 ∧ 1607494202 < 2147483647) ∧ (2141385593 < 2147483647 ∧ 540773558 < 2147483647); omega) (by rfl)
#print axioms mul05
theorem add05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1642986222#u32 855120263#u32 24802873#u32 1074150637#u32) c05=ok (q 319073557#u32 1484004661#u32 474108390#u32 1596979689#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1642986222 < 2147483647 ∧ 855120263 < 2147483647) ∧ (24802873 < 2147483647 ∧ 1074150637 < 2147483647); omega) canonical05 (by rfl)
#print axioms add05
theorem mul04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 319073557#u32 1484004661#u32 474108390#u32 1596979689#u32) (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32)=ok (q 703268045#u32 575912839#u32 1417991342#u32 1291727972#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (319073557 < 2147483647 ∧ 1484004661 < 2147483647) ∧ (474108390 < 2147483647 ∧ 1596979689 < 2147483647); omega) (by change (1817229702 < 2147483647 ∧ 1607494202 < 2147483647) ∧ (2141385593 < 2147483647 ∧ 540773558 < 2147483647); omega) (by rfl)
#print axioms mul04
theorem add04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 703268045#u32 575912839#u32 1417991342#u32 1291727972#u32) c04=ok (q 365943003#u32 1361913376#u32 1416270955#u32 849981874#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (703268045 < 2147483647 ∧ 575912839 < 2147483647) ∧ (1417991342 < 2147483647 ∧ 1291727972 < 2147483647); omega) canonical04 (by rfl)
#print axioms add04
theorem mul03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 365943003#u32 1361913376#u32 1416270955#u32 849981874#u32) (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32)=ok (q 1674647292#u32 140165116#u32 2046786836#u32 1417860719#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (365943003 < 2147483647 ∧ 1361913376 < 2147483647) ∧ (1416270955 < 2147483647 ∧ 849981874 < 2147483647); omega) (by change (1817229702 < 2147483647 ∧ 1607494202 < 2147483647) ∧ (2141385593 < 2147483647 ∧ 540773558 < 2147483647); omega) (by rfl)
#print axioms mul03
theorem add03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1674647292#u32 140165116#u32 2046786836#u32 1417860719#u32) c03=ok (q 1324983802#u32 442440862#u32 2000769114#u32 333444603#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1674647292 < 2147483647 ∧ 140165116 < 2147483647) ∧ (2046786836 < 2147483647 ∧ 1417860719 < 2147483647); omega) canonical03 (by rfl)
#print axioms add03
theorem mul02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1324983802#u32 442440862#u32 2000769114#u32 333444603#u32) (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32)=ok (q 700361776#u32 979766980#u32 1393581678#u32 1138562195#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1324983802 < 2147483647 ∧ 442440862 < 2147483647) ∧ (2000769114 < 2147483647 ∧ 333444603 < 2147483647); omega) (by change (1817229702 < 2147483647 ∧ 1607494202 < 2147483647) ∧ (2141385593 < 2147483647 ∧ 540773558 < 2147483647); omega) (by rfl)
#print axioms mul02
theorem add02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 700361776#u32 979766980#u32 1393581678#u32 1138562195#u32) c02=ok (q 882386297#u32 434296398#u32 194302947#u32 2046841735#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (700361776 < 2147483647 ∧ 979766980 < 2147483647) ∧ (1393581678 < 2147483647 ∧ 1138562195 < 2147483647); omega) canonical02 (by rfl)
#print axioms add02
theorem mul01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 882386297#u32 434296398#u32 194302947#u32 2046841735#u32) (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32)=ok (q 42963247#u32 1834658185#u32 597742841#u32 454982269#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (882386297 < 2147483647 ∧ 434296398 < 2147483647) ∧ (194302947 < 2147483647 ∧ 2046841735 < 2147483647); omega) (by change (1817229702 < 2147483647 ∧ 1607494202 < 2147483647) ∧ (2141385593 < 2147483647 ∧ 540773558 < 2147483647); omega) (by rfl)
#print axioms mul01
theorem add01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 42963247#u32 1834658185#u32 597742841#u32 454982269#u32) c01=ok (q 1760902635#u32 538325118#u32 20360536#u32 2119918731#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (42963247 < 2147483647 ∧ 1834658185 < 2147483647) ∧ (597742841 < 2147483647 ∧ 454982269 < 2147483647); omega) canonical01 (by rfl)
#print axioms add01
theorem mul00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1760902635#u32 538325118#u32 20360536#u32 2119918731#u32) (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32)=ok (q 938812346#u32 1158608638#u32 3391001#u32 477836560#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1760902635 < 2147483647 ∧ 538325118 < 2147483647) ∧ (20360536 < 2147483647 ∧ 2119918731 < 2147483647); omega) (by change (1817229702 < 2147483647 ∧ 1607494202 < 2147483647) ∧ (2141385593 < 2147483647 ∧ 540773558 < 2147483647); omega) (by rfl)
#print axioms mul00
theorem add00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 938812346#u32 1158608638#u32 3391001#u32 477836560#u32) c00=ok (q 1410821193#u32 240233113#u32 78327821#u32 166794812#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (938812346 < 2147483647 ∧ 1158608638 < 2147483647) ∧ (3391001 < 2147483647 ∧ 477836560 < 2147483647); omega) canonical00 (by rfl)
#print axioms add00
def final : Q := (q 1410821193#u32 240233113#u32 78327821#u32 166794812#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 2#usize 14#usize initial 0#usize final := by
  refine .step (by change 14>0; omega) (JFr_IndexArithmetic.sub 14#usize 13#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32) from rfl) mul13 (show Array.index_usize p 13#usize=ok c13 from rfl) add13 ?_
  refine .step (by change 13>0; omega) (JFr_IndexArithmetic.sub 13#usize 12#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32) from rfl) mul12 (show Array.index_usize p 12#usize=ok c12 from rfl) add12 ?_
  refine .step (by change 12>0; omega) (JFr_IndexArithmetic.sub 12#usize 11#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32) from rfl) mul11 (show Array.index_usize p 11#usize=ok c11 from rfl) add11 ?_
  refine .step (by change 11>0; omega) (JFr_IndexArithmetic.sub 11#usize 10#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32) from rfl) mul10 (show Array.index_usize p 10#usize=ok c10 from rfl) add10 ?_
  refine .step (by change 10>0; omega) (JFr_IndexArithmetic.sub 10#usize 9#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32) from rfl) mul09 (show Array.index_usize p 9#usize=ok c09 from rfl) add09 ?_
  refine .step (by change 9>0; omega) (JFr_IndexArithmetic.sub 9#usize 8#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32) from rfl) mul08 (show Array.index_usize p 8#usize=ok c08 from rfl) add08 ?_
  refine .step (by change 8>0; omega) (JFr_IndexArithmetic.sub 8#usize 7#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32) from rfl) mul07 (show Array.index_usize p 7#usize=ok c07 from rfl) add07 ?_
  refine .step (by change 7>0; omega) (JFr_IndexArithmetic.sub 7#usize 6#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32) from rfl) mul06 (show Array.index_usize p 6#usize=ok c06 from rfl) add06 ?_
  refine .step (by change 6>0; omega) (JFr_IndexArithmetic.sub 6#usize 5#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32) from rfl) mul05 (show Array.index_usize p 5#usize=ok c05 from rfl) add05 ?_
  refine .step (by change 5>0; omega) (JFr_IndexArithmetic.sub 5#usize 4#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32) from rfl) mul04 (show Array.index_usize p 4#usize=ok c04 from rfl) add04 ?_
  refine .step (by change 4>0; omega) (JFr_IndexArithmetic.sub 4#usize 3#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32) from rfl) mul03 (show Array.index_usize p 3#usize=ok c03 from rfl) add03 ?_
  refine .step (by change 3>0; omega) (JFr_IndexArithmetic.sub 3#usize 2#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32) from rfl) mul02 (show Array.index_usize p 2#usize=ok c02 from rfl) add02 ?_
  refine .step (by change 2>0; omega) (JFr_IndexArithmetic.sub 2#usize 1#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32) from rfl) mul01 (show Array.index_usize p 1#usize=ok c01 from rfl) add01 ?_
  refine .step (by change 1>0; omega) (JFr_IndexArithmetic.sub 1#usize 0#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32) from rfl) mul00 (show Array.index_usize p 0#usize=ok c00 from rfl) add00 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner02_1
