import NDO_JFr_Data04
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner04_0
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data04
def initial : Q := (q 0#u32 0#u32 0#u32 0#u32)
theorem mul27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 0#u32 0#u32 0#u32 0#u32) (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32)=ok (q 0#u32 0#u32 0#u32 0#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) (by change (763754670 < 2147483647 ∧ 31463458 < 2147483647) ∧ (1727849165 < 2147483647 ∧ 1028580563 < 2147483647); omega) (by rfl)
#print axioms mul27
theorem add27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 0#u32 0#u32 0#u32 0#u32) c27=ok (q 1634072623#u32 469678916#u32 1641267273#u32 309303516#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) canonical27 (by rfl)
#print axioms add27
theorem mul26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1634072623#u32 469678916#u32 1641267273#u32 309303516#u32) (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32)=ok (q 1740111945#u32 2001209612#u32 277120843#u32 219230287#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1634072623 < 2147483647 ∧ 469678916 < 2147483647) ∧ (1641267273 < 2147483647 ∧ 309303516 < 2147483647); omega) (by change (763754670 < 2147483647 ∧ 31463458 < 2147483647) ∧ (1727849165 < 2147483647 ∧ 1028580563 < 2147483647); omega) (by rfl)
#print axioms mul26
theorem add26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1740111945#u32 2001209612#u32 277120843#u32 219230287#u32) c26=ok (q 621739#u32 829414022#u32 125107415#u32 393858960#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1740111945 < 2147483647 ∧ 2001209612 < 2147483647) ∧ (277120843 < 2147483647 ∧ 219230287 < 2147483647); omega) canonical26 (by rfl)
#print axioms add26
theorem mul25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 621739#u32 829414022#u32 125107415#u32 393858960#u32) (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32)=ok (q 1358201531#u32 417172414#u32 562308255#u32 1604672803#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (621739 < 2147483647 ∧ 829414022 < 2147483647) ∧ (125107415 < 2147483647 ∧ 393858960 < 2147483647); omega) (by change (763754670 < 2147483647 ∧ 31463458 < 2147483647) ∧ (1727849165 < 2147483647 ∧ 1028580563 < 2147483647); omega) (by rfl)
#print axioms mul25
theorem add25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1358201531#u32 417172414#u32 562308255#u32 1604672803#u32) c25=ok (q 1728357748#u32 172643668#u32 683923675#u32 1296429209#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1358201531 < 2147483647 ∧ 417172414 < 2147483647) ∧ (562308255 < 2147483647 ∧ 1604672803 < 2147483647); omega) canonical25 (by rfl)
#print axioms add25
theorem mul24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1728357748#u32 172643668#u32 683923675#u32 1296429209#u32) (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32)=ok (q 738343967#u32 62412516#u32 2125539699#u32 1322771422#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1728357748 < 2147483647 ∧ 172643668 < 2147483647) ∧ (683923675 < 2147483647 ∧ 1296429209 < 2147483647); omega) (by change (763754670 < 2147483647 ∧ 31463458 < 2147483647) ∧ (1727849165 < 2147483647 ∧ 1028580563 < 2147483647); omega) (by rfl)
#print axioms mul24
theorem add24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 738343967#u32 62412516#u32 2125539699#u32 1322771422#u32) c24=ok (q 1402046752#u32 50389027#u32 647053845#u32 1118620128#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (738343967 < 2147483647 ∧ 62412516 < 2147483647) ∧ (2125539699 < 2147483647 ∧ 1322771422 < 2147483647); omega) canonical24 (by rfl)
#print axioms add24
theorem mul23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1402046752#u32 50389027#u32 647053845#u32 1118620128#u32) (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32)=ok (q 688827943#u32 498494009#u32 1885979140#u32 114461584#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1402046752 < 2147483647 ∧ 50389027 < 2147483647) ∧ (647053845 < 2147483647 ∧ 1118620128 < 2147483647); omega) (by change (763754670 < 2147483647 ∧ 31463458 < 2147483647) ∧ (1727849165 < 2147483647 ∧ 1028580563 < 2147483647); omega) (by rfl)
#print axioms mul23
theorem add23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 688827943#u32 498494009#u32 1885979140#u32 114461584#u32) c23=ok (q 1616692290#u32 1578482446#u32 1899523659#u32 943323716#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (688827943 < 2147483647 ∧ 498494009 < 2147483647) ∧ (1885979140 < 2147483647 ∧ 114461584 < 2147483647); omega) canonical23 (by rfl)
#print axioms add23
theorem mul22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1616692290#u32 1578482446#u32 1899523659#u32 943323716#u32) (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32)=ok (q 849397901#u32 880395675#u32 237515471#u32 1490291223#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1616692290 < 2147483647 ∧ 1578482446 < 2147483647) ∧ (1899523659 < 2147483647 ∧ 943323716 < 2147483647); omega) (by change (763754670 < 2147483647 ∧ 31463458 < 2147483647) ∧ (1727849165 < 2147483647 ∧ 1028580563 < 2147483647); omega) (by rfl)
#print axioms mul22
theorem add22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 849397901#u32 880395675#u32 237515471#u32 1490291223#u32) c22=ok (q 1504415625#u32 1264838888#u32 656492799#u32 1433654025#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (849397901 < 2147483647 ∧ 880395675 < 2147483647) ∧ (237515471 < 2147483647 ∧ 1490291223 < 2147483647); omega) canonical22 (by rfl)
#print axioms add22
theorem mul21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1504415625#u32 1264838888#u32 656492799#u32 1433654025#u32) (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32)=ok (q 1341773605#u32 602638653#u32 670564814#u32 331803026#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1504415625 < 2147483647 ∧ 1264838888 < 2147483647) ∧ (656492799 < 2147483647 ∧ 1433654025 < 2147483647); omega) (by change (763754670 < 2147483647 ∧ 31463458 < 2147483647) ∧ (1727849165 < 2147483647 ∧ 1028580563 < 2147483647); omega) (by rfl)
#print axioms mul21
theorem add21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1341773605#u32 602638653#u32 670564814#u32 331803026#u32) c21=ok (q 1193547826#u32 634388781#u32 1032992064#u32 1108378626#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1341773605 < 2147483647 ∧ 602638653 < 2147483647) ∧ (670564814 < 2147483647 ∧ 331803026 < 2147483647); omega) canonical21 (by rfl)
#print axioms add21
theorem mul20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1193547826#u32 634388781#u32 1032992064#u32 1108378626#u32) (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32)=ok (q 338323002#u32 1996770362#u32 1597759626#u32 2044937744#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1193547826 < 2147483647 ∧ 634388781 < 2147483647) ∧ (1032992064 < 2147483647 ∧ 1108378626 < 2147483647); omega) (by change (763754670 < 2147483647 ∧ 31463458 < 2147483647) ∧ (1727849165 < 2147483647 ∧ 1028580563 < 2147483647); omega) (by rfl)
#print axioms mul20
theorem add20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 338323002#u32 1996770362#u32 1597759626#u32 2044937744#u32) c20=ok (q 524918716#u32 190369865#u32 1112767040#u32 559236782#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (338323002 < 2147483647 ∧ 1996770362 < 2147483647) ∧ (1597759626 < 2147483647 ∧ 2044937744 < 2147483647); omega) canonical20 (by rfl)
#print axioms add20
theorem mul19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 524918716#u32 190369865#u32 1112767040#u32 559236782#u32) (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32)=ok (q 1834150156#u32 2083848737#u32 1378123336#u32 23551691#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (524918716 < 2147483647 ∧ 190369865 < 2147483647) ∧ (1112767040 < 2147483647 ∧ 559236782 < 2147483647); omega) (by change (763754670 < 2147483647 ∧ 31463458 < 2147483647) ∧ (1727849165 < 2147483647 ∧ 1028580563 < 2147483647); omega) (by rfl)
#print axioms mul19
theorem add19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1834150156#u32 2083848737#u32 1378123336#u32 23551691#u32) c19=ok (q 1428350354#u32 617592238#u32 615640660#u32 1151321723#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1834150156 < 2147483647 ∧ 2083848737 < 2147483647) ∧ (1378123336 < 2147483647 ∧ 23551691 < 2147483647); omega) canonical19 (by rfl)
#print axioms add19
theorem mul18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1428350354#u32 617592238#u32 615640660#u32 1151321723#u32) (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32)=ok (q 1927196155#u32 926088085#u32 1664770983#u32 1967974785#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1428350354 < 2147483647 ∧ 617592238 < 2147483647) ∧ (615640660 < 2147483647 ∧ 1151321723 < 2147483647); omega) (by change (763754670 < 2147483647 ∧ 31463458 < 2147483647) ∧ (1727849165 < 2147483647 ∧ 1028580563 < 2147483647); omega) (by rfl)
#print axioms mul18
theorem add18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1927196155#u32 926088085#u32 1664770983#u32 1967974785#u32) c18=ok (q 1363075145#u32 1242681365#u32 1328163488#u32 1636668706#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1927196155 < 2147483647 ∧ 926088085 < 2147483647) ∧ (1664770983 < 2147483647 ∧ 1967974785 < 2147483647); omega) canonical18 (by rfl)
#print axioms add18
theorem mul17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1363075145#u32 1242681365#u32 1328163488#u32 1636668706#u32) (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32)=ok (q 1327139647#u32 1008765795#u32 1761088690#u32 1137205769#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1363075145 < 2147483647 ∧ 1242681365 < 2147483647) ∧ (1328163488 < 2147483647 ∧ 1636668706 < 2147483647); omega) (by change (763754670 < 2147483647 ∧ 31463458 < 2147483647) ∧ (1727849165 < 2147483647 ∧ 1028580563 < 2147483647); omega) (by rfl)
#print axioms mul17
theorem add17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1327139647#u32 1008765795#u32 1761088690#u32 1137205769#u32) c17=ok (q 604084098#u32 1356840079#u32 1159429408#u32 77112685#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1327139647 < 2147483647 ∧ 1008765795 < 2147483647) ∧ (1761088690 < 2147483647 ∧ 1137205769 < 2147483647); omega) canonical17 (by rfl)
#print axioms add17
theorem mul16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 604084098#u32 1356840079#u32 1159429408#u32 77112685#u32) (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32)=ok (q 256992740#u32 619755840#u32 1815207148#u32 1731935842#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (604084098 < 2147483647 ∧ 1356840079 < 2147483647) ∧ (1159429408 < 2147483647 ∧ 77112685 < 2147483647); omega) (by change (763754670 < 2147483647 ∧ 31463458 < 2147483647) ∧ (1727849165 < 2147483647 ∧ 1028580563 < 2147483647); omega) (by rfl)
#print axioms mul16
theorem add16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 256992740#u32 619755840#u32 1815207148#u32 1731935842#u32) c16=ok (q 1210513887#u32 1737906852#u32 1127567951#u32 759105482#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (256992740 < 2147483647 ∧ 619755840 < 2147483647) ∧ (1815207148 < 2147483647 ∧ 1731935842 < 2147483647); omega) canonical16 (by rfl)
#print axioms add16
theorem mul15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1210513887#u32 1737906852#u32 1127567951#u32 759105482#u32) (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32)=ok (q 799688083#u32 522688262#u32 462106364#u32 1521769032#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1210513887 < 2147483647 ∧ 1737906852 < 2147483647) ∧ (1127567951 < 2147483647 ∧ 759105482 < 2147483647); omega) (by change (763754670 < 2147483647 ∧ 31463458 < 2147483647) ∧ (1727849165 < 2147483647 ∧ 1028580563 < 2147483647); omega) (by rfl)
#print axioms mul15
theorem add15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 799688083#u32 522688262#u32 462106364#u32 1521769032#u32) c15=ok (q 1237358007#u32 1277898453#u32 1835084042#u32 1956558091#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (799688083 < 2147483647 ∧ 522688262 < 2147483647) ∧ (462106364 < 2147483647 ∧ 1521769032 < 2147483647); omega) canonical15 (by rfl)
#print axioms add15
theorem mul14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1237358007#u32 1277898453#u32 1835084042#u32 1956558091#u32) (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32)=ok (q 1161391012#u32 624128817#u32 263292520#u32 1066812199#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1237358007 < 2147483647 ∧ 1277898453 < 2147483647) ∧ (1835084042 < 2147483647 ∧ 1956558091 < 2147483647); omega) (by change (763754670 < 2147483647 ∧ 31463458 < 2147483647) ∧ (1727849165 < 2147483647 ∧ 1028580563 < 2147483647); omega) (by rfl)
#print axioms mul14
theorem add14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1161391012#u32 624128817#u32 263292520#u32 1066812199#u32) c14=ok (q 1718921177#u32 777043832#u32 776900213#u32 1727828662#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1161391012 < 2147483647 ∧ 624128817 < 2147483647) ∧ (263292520 < 2147483647 ∧ 1066812199 < 2147483647); omega) canonical14 (by rfl)
#print axioms add14
def final : Q := (q 1718921177#u32 777043832#u32 776900213#u32 1727828662#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 4#usize 28#usize initial 14#usize final := by
  refine .step (by change 28>0; omega) (JFr_IndexArithmetic.sub 28#usize 27#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32) from rfl) mul27 (show Array.index_usize p 27#usize=ok c27 from rfl) add27 ?_
  refine .step (by change 27>0; omega) (JFr_IndexArithmetic.sub 27#usize 26#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32) from rfl) mul26 (show Array.index_usize p 26#usize=ok c26 from rfl) add26 ?_
  refine .step (by change 26>0; omega) (JFr_IndexArithmetic.sub 26#usize 25#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32) from rfl) mul25 (show Array.index_usize p 25#usize=ok c25 from rfl) add25 ?_
  refine .step (by change 25>0; omega) (JFr_IndexArithmetic.sub 25#usize 24#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32) from rfl) mul24 (show Array.index_usize p 24#usize=ok c24 from rfl) add24 ?_
  refine .step (by change 24>0; omega) (JFr_IndexArithmetic.sub 24#usize 23#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32) from rfl) mul23 (show Array.index_usize p 23#usize=ok c23 from rfl) add23 ?_
  refine .step (by change 23>0; omega) (JFr_IndexArithmetic.sub 23#usize 22#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32) from rfl) mul22 (show Array.index_usize p 22#usize=ok c22 from rfl) add22 ?_
  refine .step (by change 22>0; omega) (JFr_IndexArithmetic.sub 22#usize 21#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32) from rfl) mul21 (show Array.index_usize p 21#usize=ok c21 from rfl) add21 ?_
  refine .step (by change 21>0; omega) (JFr_IndexArithmetic.sub 21#usize 20#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32) from rfl) mul20 (show Array.index_usize p 20#usize=ok c20 from rfl) add20 ?_
  refine .step (by change 20>0; omega) (JFr_IndexArithmetic.sub 20#usize 19#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32) from rfl) mul19 (show Array.index_usize p 19#usize=ok c19 from rfl) add19 ?_
  refine .step (by change 19>0; omega) (JFr_IndexArithmetic.sub 19#usize 18#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32) from rfl) mul18 (show Array.index_usize p 18#usize=ok c18 from rfl) add18 ?_
  refine .step (by change 18>0; omega) (JFr_IndexArithmetic.sub 18#usize 17#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32) from rfl) mul17 (show Array.index_usize p 17#usize=ok c17 from rfl) add17 ?_
  refine .step (by change 17>0; omega) (JFr_IndexArithmetic.sub 17#usize 16#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32) from rfl) mul16 (show Array.index_usize p 16#usize=ok c16 from rfl) add16 ?_
  refine .step (by change 16>0; omega) (JFr_IndexArithmetic.sub 16#usize 15#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32) from rfl) mul15 (show Array.index_usize p 15#usize=ok c15 from rfl) add15 ?_
  refine .step (by change 15>0; omega) (JFr_IndexArithmetic.sub 15#usize 14#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32) from rfl) mul14 (show Array.index_usize p 14#usize=ok c14 from rfl) add14 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner04_0
