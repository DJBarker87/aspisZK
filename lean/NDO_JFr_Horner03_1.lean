import NDO_JFr_Data03
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner03_1
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data03
def initial : Q := (q 963747040#u32 1926430192#u32 447166026#u32 2096645527#u32)
theorem mul13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 963747040#u32 1926430192#u32 447166026#u32 2096645527#u32) (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32)=ok (q 2085009334#u32 317081746#u32 1915151500#u32 1347198038#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (963747040 < 2147483647 ∧ 1926430192 < 2147483647) ∧ (447166026 < 2147483647 ∧ 2096645527 < 2147483647); omega) (by change (1142413086 < 2147483647 ∧ 2006134641 < 2147483647) ∧ (1686703278 < 2147483647 ∧ 2011383024 < 2147483647); omega) (by rfl)
#print axioms mul13
theorem add13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2085009334#u32 317081746#u32 1915151500#u32 1347198038#u32) c13=ok (q 1234556694#u32 1721917229#u32 1209134966#u32 724474079#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2085009334 < 2147483647 ∧ 317081746 < 2147483647) ∧ (1915151500 < 2147483647 ∧ 1347198038 < 2147483647); omega) canonical13 (by rfl)
#print axioms add13
theorem mul12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1234556694#u32 1721917229#u32 1209134966#u32 724474079#u32) (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32)=ok (q 2050104991#u32 1687820063#u32 974548239#u32 761259306#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1234556694 < 2147483647 ∧ 1721917229 < 2147483647) ∧ (1209134966 < 2147483647 ∧ 724474079 < 2147483647); omega) (by change (1142413086 < 2147483647 ∧ 2006134641 < 2147483647) ∧ (1686703278 < 2147483647 ∧ 2011383024 < 2147483647); omega) (by rfl)
#print axioms mul12
theorem add12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2050104991#u32 1687820063#u32 974548239#u32 761259306#u32) c12=ok (q 598341392#u32 511566105#u32 154391220#u32 883441184#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2050104991 < 2147483647 ∧ 1687820063 < 2147483647) ∧ (974548239 < 2147483647 ∧ 761259306 < 2147483647); omega) canonical12 (by rfl)
#print axioms add12
theorem mul11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 598341392#u32 511566105#u32 154391220#u32 883441184#u32) (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32)=ok (q 67538446#u32 904993418#u32 1812113449#u32 441091500#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (598341392 < 2147483647 ∧ 511566105 < 2147483647) ∧ (154391220 < 2147483647 ∧ 883441184 < 2147483647); omega) (by change (1142413086 < 2147483647 ∧ 2006134641 < 2147483647) ∧ (1686703278 < 2147483647 ∧ 2011383024 < 2147483647); omega) (by rfl)
#print axioms mul11
theorem add11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 67538446#u32 904993418#u32 1812113449#u32 441091500#u32) c11=ok (q 418127548#u32 691124844#u32 885110600#u32 937312994#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (67538446 < 2147483647 ∧ 904993418 < 2147483647) ∧ (1812113449 < 2147483647 ∧ 441091500 < 2147483647); omega) canonical11 (by rfl)
#print axioms add11
theorem mul10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 418127548#u32 691124844#u32 885110600#u32 937312994#u32) (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32)=ok (q 807079148#u32 1671598714#u32 1836044651#u32 1514815588#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (418127548 < 2147483647 ∧ 691124844 < 2147483647) ∧ (885110600 < 2147483647 ∧ 937312994 < 2147483647); omega) (by change (1142413086 < 2147483647 ∧ 2006134641 < 2147483647) ∧ (1686703278 < 2147483647 ∧ 2011383024 < 2147483647); omega) (by rfl)
#print axioms mul10
theorem add10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 807079148#u32 1671598714#u32 1836044651#u32 1514815588#u32) c10=ok (q 1093530830#u32 1447530673#u32 282469307#u32 110315218#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (807079148 < 2147483647 ∧ 1671598714 < 2147483647) ∧ (1836044651 < 2147483647 ∧ 1514815588 < 2147483647); omega) canonical10 (by rfl)
#print axioms add10
theorem mul09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1093530830#u32 1447530673#u32 282469307#u32 110315218#u32) (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32)=ok (q 2055348055#u32 2063355336#u32 1408970657#u32 369576317#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1093530830 < 2147483647 ∧ 1447530673 < 2147483647) ∧ (282469307 < 2147483647 ∧ 110315218 < 2147483647); omega) (by change (1142413086 < 2147483647 ∧ 2006134641 < 2147483647) ∧ (1686703278 < 2147483647 ∧ 2011383024 < 2147483647); omega) (by rfl)
#print axioms mul09
theorem add09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2055348055#u32 2063355336#u32 1408970657#u32 369576317#u32) c09=ok (q 504012630#u32 782546431#u32 75631633#u32 2031667993#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2055348055 < 2147483647 ∧ 2063355336 < 2147483647) ∧ (1408970657 < 2147483647 ∧ 369576317 < 2147483647); omega) canonical09 (by rfl)
#print axioms add09
theorem mul08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 504012630#u32 782546431#u32 75631633#u32 2031667993#u32) (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32)=ok (q 1912529112#u32 614825466#u32 2035651308#u32 1274987708#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (504012630 < 2147483647 ∧ 782546431 < 2147483647) ∧ (75631633 < 2147483647 ∧ 2031667993 < 2147483647); omega) (by change (1142413086 < 2147483647 ∧ 2006134641 < 2147483647) ∧ (1686703278 < 2147483647 ∧ 2011383024 < 2147483647); omega) (by rfl)
#print axioms mul08
theorem add08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1912529112#u32 614825466#u32 2035651308#u32 1274987708#u32) c08=ok (q 76938434#u32 1545719895#u32 1372357456#u32 1507758250#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1912529112 < 2147483647 ∧ 614825466 < 2147483647) ∧ (2035651308 < 2147483647 ∧ 1274987708 < 2147483647); omega) canonical08 (by rfl)
#print axioms add08
theorem mul07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 76938434#u32 1545719895#u32 1372357456#u32 1507758250#u32) (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32)=ok (q 1429198860#u32 718788958#u32 1917889121#u32 1126325741#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (76938434 < 2147483647 ∧ 1545719895 < 2147483647) ∧ (1372357456 < 2147483647 ∧ 1507758250 < 2147483647); omega) (by change (1142413086 < 2147483647 ∧ 2006134641 < 2147483647) ∧ (1686703278 < 2147483647 ∧ 2011383024 < 2147483647); omega) (by rfl)
#print axioms mul07
theorem add07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1429198860#u32 718788958#u32 1917889121#u32 1126325741#u32) c07=ok (q 1962836325#u32 163819688#u32 1467318143#u32 326485596#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1429198860 < 2147483647 ∧ 718788958 < 2147483647) ∧ (1917889121 < 2147483647 ∧ 1126325741 < 2147483647); omega) canonical07 (by rfl)
#print axioms add07
theorem mul06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1962836325#u32 163819688#u32 1467318143#u32 326485596#u32) (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32)=ok (q 1932161358#u32 1633977112#u32 1927103465#u32 585227248#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1962836325 < 2147483647 ∧ 163819688 < 2147483647) ∧ (1467318143 < 2147483647 ∧ 326485596 < 2147483647); omega) (by change (1142413086 < 2147483647 ∧ 2006134641 < 2147483647) ∧ (1686703278 < 2147483647 ∧ 2011383024 < 2147483647); omega) (by rfl)
#print axioms mul06
theorem add06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1932161358#u32 1633977112#u32 1927103465#u32 585227248#u32) c06=ok (q 101812190#u32 1810764713#u32 1468318416#u32 112476454#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1932161358 < 2147483647 ∧ 1633977112 < 2147483647) ∧ (1927103465 < 2147483647 ∧ 585227248 < 2147483647); omega) canonical06 (by rfl)
#print axioms add06
theorem mul05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 101812190#u32 1810764713#u32 1468318416#u32 112476454#u32) (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32)=ok (q 1934082550#u32 294865920#u32 525072976#u32 1868893974#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (101812190 < 2147483647 ∧ 1810764713 < 2147483647) ∧ (1468318416 < 2147483647 ∧ 112476454 < 2147483647); omega) (by change (1142413086 < 2147483647 ∧ 2006134641 < 2147483647) ∧ (1686703278 < 2147483647 ∧ 2011383024 < 2147483647); omega) (by rfl)
#print axioms mul05
theorem add05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1934082550#u32 294865920#u32 525072976#u32 1868893974#u32) c05=ok (q 202455067#u32 1009376607#u32 1259755218#u32 535672631#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1934082550 < 2147483647 ∧ 294865920 < 2147483647) ∧ (525072976 < 2147483647 ∧ 1868893974 < 2147483647); omega) canonical05 (by rfl)
#print axioms add05
theorem mul04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 202455067#u32 1009376607#u32 1259755218#u32 535672631#u32) (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32)=ok (q 1589076980#u32 887289464#u32 402520009#u32 1550262488#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (202455067 < 2147483647 ∧ 1009376607 < 2147483647) ∧ (1259755218 < 2147483647 ∧ 535672631 < 2147483647); omega) (by change (1142413086 < 2147483647 ∧ 2006134641 < 2147483647) ∧ (1686703278 < 2147483647 ∧ 2011383024 < 2147483647); omega) (by rfl)
#print axioms mul04
theorem add04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1589076980#u32 887289464#u32 402520009#u32 1550262488#u32) c04=ok (q 1693811392#u32 484758870#u32 149422894#u32 485826455#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1589076980 < 2147483647 ∧ 887289464 < 2147483647) ∧ (402520009 < 2147483647 ∧ 1550262488 < 2147483647); omega) canonical04 (by rfl)
#print axioms add04
theorem mul03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1693811392#u32 484758870#u32 149422894#u32 485826455#u32) (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32)=ok (q 1650083712#u32 1132862015#u32 2088759949#u32 736804977#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1693811392 < 2147483647 ∧ 484758870 < 2147483647) ∧ (149422894 < 2147483647 ∧ 485826455 < 2147483647); omega) (by change (1142413086 < 2147483647 ∧ 2006134641 < 2147483647) ∧ (1686703278 < 2147483647 ∧ 2011383024 < 2147483647); omega) (by rfl)
#print axioms mul03
theorem add03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1650083712#u32 1132862015#u32 2088759949#u32 736804977#u32) c03=ok (q 1139058148#u32 15439713#u32 724311485#u32 1785647266#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1650083712 < 2147483647 ∧ 1132862015 < 2147483647) ∧ (2088759949 < 2147483647 ∧ 736804977 < 2147483647); omega) canonical03 (by rfl)
#print axioms add03
theorem mul02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1139058148#u32 15439713#u32 724311485#u32 1785647266#u32) (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32)=ok (q 1296559105#u32 1674625779#u32 1728044874#u32 305552595#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1139058148 < 2147483647 ∧ 15439713 < 2147483647) ∧ (724311485 < 2147483647 ∧ 1785647266 < 2147483647); omega) (by change (1142413086 < 2147483647 ∧ 2006134641 < 2147483647) ∧ (1686703278 < 2147483647 ∧ 2011383024 < 2147483647); omega) (by rfl)
#print axioms mul02
theorem add02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1296559105#u32 1674625779#u32 1728044874#u32 305552595#u32) c02=ok (q 1152697983#u32 2036202757#u32 1443906152#u32 1985860280#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1296559105 < 2147483647 ∧ 1674625779 < 2147483647) ∧ (1728044874 < 2147483647 ∧ 305552595 < 2147483647); omega) canonical02 (by rfl)
#print axioms add02
theorem mul01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1152697983#u32 2036202757#u32 1443906152#u32 1985860280#u32) (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32)=ok (q 1137417873#u32 166580227#u32 1814359040#u32 1457328231#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1152697983 < 2147483647 ∧ 2036202757 < 2147483647) ∧ (1443906152 < 2147483647 ∧ 1985860280 < 2147483647); omega) (by change (1142413086 < 2147483647 ∧ 2006134641 < 2147483647) ∧ (1686703278 < 2147483647 ∧ 2011383024 < 2147483647); omega) (by rfl)
#print axioms mul01
theorem add01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1137417873#u32 166580227#u32 1814359040#u32 1457328231#u32) c01=ok (q 594838622#u32 591188972#u32 1126230375#u32 34098553#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1137417873 < 2147483647 ∧ 166580227 < 2147483647) ∧ (1814359040 < 2147483647 ∧ 1457328231 < 2147483647); omega) canonical01 (by rfl)
#print axioms add01
theorem mul00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 594838622#u32 591188972#u32 1126230375#u32 34098553#u32) (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32)=ok (q 1500707510#u32 1608158901#u32 428491385#u32 141420509#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (594838622 < 2147483647 ∧ 591188972 < 2147483647) ∧ (1126230375 < 2147483647 ∧ 34098553 < 2147483647); omega) (by change (1142413086 < 2147483647 ∧ 2006134641 < 2147483647) ∧ (1686703278 < 2147483647 ∧ 2011383024 < 2147483647); omega) (by rfl)
#print axioms mul00
theorem add00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1500707510#u32 1608158901#u32 428491385#u32 141420509#u32) c00=ok (q 447580414#u32 662377318#u32 2092951356#u32 1893445069#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1500707510 < 2147483647 ∧ 1608158901 < 2147483647) ∧ (428491385 < 2147483647 ∧ 141420509 < 2147483647); omega) canonical00 (by rfl)
#print axioms add00
def final : Q := (q 447580414#u32 662377318#u32 2092951356#u32 1893445069#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 3#usize 14#usize initial 0#usize final := by
  refine .step (by change 14>0; omega) (JFr_IndexArithmetic.sub 14#usize 13#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32) from rfl) mul13 (show Array.index_usize p 13#usize=ok c13 from rfl) add13 ?_
  refine .step (by change 13>0; omega) (JFr_IndexArithmetic.sub 13#usize 12#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32) from rfl) mul12 (show Array.index_usize p 12#usize=ok c12 from rfl) add12 ?_
  refine .step (by change 12>0; omega) (JFr_IndexArithmetic.sub 12#usize 11#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32) from rfl) mul11 (show Array.index_usize p 11#usize=ok c11 from rfl) add11 ?_
  refine .step (by change 11>0; omega) (JFr_IndexArithmetic.sub 11#usize 10#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32) from rfl) mul10 (show Array.index_usize p 10#usize=ok c10 from rfl) add10 ?_
  refine .step (by change 10>0; omega) (JFr_IndexArithmetic.sub 10#usize 9#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32) from rfl) mul09 (show Array.index_usize p 9#usize=ok c09 from rfl) add09 ?_
  refine .step (by change 9>0; omega) (JFr_IndexArithmetic.sub 9#usize 8#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32) from rfl) mul08 (show Array.index_usize p 8#usize=ok c08 from rfl) add08 ?_
  refine .step (by change 8>0; omega) (JFr_IndexArithmetic.sub 8#usize 7#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32) from rfl) mul07 (show Array.index_usize p 7#usize=ok c07 from rfl) add07 ?_
  refine .step (by change 7>0; omega) (JFr_IndexArithmetic.sub 7#usize 6#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32) from rfl) mul06 (show Array.index_usize p 6#usize=ok c06 from rfl) add06 ?_
  refine .step (by change 6>0; omega) (JFr_IndexArithmetic.sub 6#usize 5#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32) from rfl) mul05 (show Array.index_usize p 5#usize=ok c05 from rfl) add05 ?_
  refine .step (by change 5>0; omega) (JFr_IndexArithmetic.sub 5#usize 4#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32) from rfl) mul04 (show Array.index_usize p 4#usize=ok c04 from rfl) add04 ?_
  refine .step (by change 4>0; omega) (JFr_IndexArithmetic.sub 4#usize 3#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32) from rfl) mul03 (show Array.index_usize p 3#usize=ok c03 from rfl) add03 ?_
  refine .step (by change 3>0; omega) (JFr_IndexArithmetic.sub 3#usize 2#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32) from rfl) mul02 (show Array.index_usize p 2#usize=ok c02 from rfl) add02 ?_
  refine .step (by change 2>0; omega) (JFr_IndexArithmetic.sub 2#usize 1#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32) from rfl) mul01 (show Array.index_usize p 1#usize=ok c01 from rfl) add01 ?_
  refine .step (by change 1>0; omega) (JFr_IndexArithmetic.sub 1#usize 0#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32) from rfl) mul00 (show Array.index_usize p 0#usize=ok c00 from rfl) add00 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner03_1
