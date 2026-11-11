import NDO_JFr_Data02
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner02_0
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data02
def initial : Q := (q 0#u32 0#u32 0#u32 0#u32)
theorem mul27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 0#u32 0#u32 0#u32 0#u32) (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32)=ok (q 0#u32 0#u32 0#u32 0#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) (by change (1817229702 < 2147483647 ∧ 1607494202 < 2147483647) ∧ (2141385593 < 2147483647 ∧ 540773558 < 2147483647); omega) (by rfl)
#print axioms mul27
theorem add27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 0#u32 0#u32 0#u32 0#u32) c27=ok (q 1940414313#u32 326906091#u32 1314401326#u32 685818025#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) canonical27 (by rfl)
#print axioms add27
theorem mul26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1940414313#u32 326906091#u32 1314401326#u32 685818025#u32) (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32)=ok (q 1690586556#u32 1967272498#u32 2029311235#u32 638243163#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1940414313 < 2147483647 ∧ 326906091 < 2147483647) ∧ (1314401326 < 2147483647 ∧ 685818025 < 2147483647); omega) (by change (1817229702 < 2147483647 ∧ 1607494202 < 2147483647) ∧ (2141385593 < 2147483647 ∧ 540773558 < 2147483647); omega) (by rfl)
#print axioms mul26
theorem add26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1690586556#u32 1967272498#u32 2029311235#u32 638243163#u32) c26=ok (q 279507395#u32 2119407062#u32 1608426228#u32 1265290131#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1690586556 < 2147483647 ∧ 1967272498 < 2147483647) ∧ (2029311235 < 2147483647 ∧ 638243163 < 2147483647); omega) canonical26 (by rfl)
#print axioms add26
theorem mul25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 279507395#u32 2119407062#u32 1608426228#u32 1265290131#u32) (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32)=ok (q 1688227161#u32 709789175#u32 1596251478#u32 155710847#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (279507395 < 2147483647 ∧ 2119407062 < 2147483647) ∧ (1608426228 < 2147483647 ∧ 1265290131 < 2147483647); omega) (by change (1817229702 < 2147483647 ∧ 1607494202 < 2147483647) ∧ (2141385593 < 2147483647 ∧ 540773558 < 2147483647); omega) (by rfl)
#print axioms mul25
theorem add25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1688227161#u32 709789175#u32 1596251478#u32 155710847#u32) c25=ok (q 2022361213#u32 711909840#u32 1971783480#u32 1968101347#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1688227161 < 2147483647 ∧ 709789175 < 2147483647) ∧ (1596251478 < 2147483647 ∧ 155710847 < 2147483647); omega) canonical25 (by rfl)
#print axioms add25
theorem mul24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2022361213#u32 711909840#u32 1971783480#u32 1968101347#u32) (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32)=ok (q 1067316303#u32 1178342468#u32 1402712285#u32 548721707#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2022361213 < 2147483647 ∧ 711909840 < 2147483647) ∧ (1971783480 < 2147483647 ∧ 1968101347 < 2147483647); omega) (by change (1817229702 < 2147483647 ∧ 1607494202 < 2147483647) ∧ (2141385593 < 2147483647 ∧ 540773558 < 2147483647); omega) (by rfl)
#print axioms mul24
theorem add24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1067316303#u32 1178342468#u32 1402712285#u32 548721707#u32) c24=ok (q 98031259#u32 178633077#u32 1911490985#u32 1341598855#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1067316303 < 2147483647 ∧ 1178342468 < 2147483647) ∧ (1402712285 < 2147483647 ∧ 548721707 < 2147483647); omega) canonical24 (by rfl)
#print axioms add24
theorem mul23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 98031259#u32 178633077#u32 1911490985#u32 1341598855#u32) (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32)=ok (q 397835751#u32 1393293649#u32 1645741652#u32 489858851#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (98031259 < 2147483647 ∧ 178633077 < 2147483647) ∧ (1911490985 < 2147483647 ∧ 1341598855 < 2147483647); omega) (by change (1817229702 < 2147483647 ∧ 1607494202 < 2147483647) ∧ (2141385593 < 2147483647 ∧ 540773558 < 2147483647); omega) (by rfl)
#print axioms mul23
theorem add23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 397835751#u32 1393293649#u32 1645741652#u32 489858851#u32) c23=ok (q 1087861827#u32 305484563#u32 1488865862#u32 1694616327#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (397835751 < 2147483647 ∧ 1393293649 < 2147483647) ∧ (1645741652 < 2147483647 ∧ 489858851 < 2147483647); omega) canonical23 (by rfl)
#print axioms add23
theorem mul22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1087861827#u32 305484563#u32 1488865862#u32 1694616327#u32) (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32)=ok (q 1823904248#u32 1749733498#u32 426567943#u32 1413532714#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1087861827 < 2147483647 ∧ 305484563 < 2147483647) ∧ (1488865862 < 2147483647 ∧ 1694616327 < 2147483647); omega) (by change (1817229702 < 2147483647 ∧ 1607494202 < 2147483647) ∧ (2141385593 < 2147483647 ∧ 540773558 < 2147483647); omega) (by rfl)
#print axioms mul22
theorem add22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1823904248#u32 1749733498#u32 426567943#u32 1413532714#u32) c22=ok (q 351056699#u32 1258656308#u32 161645433#u32 1395346597#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1823904248 < 2147483647 ∧ 1749733498 < 2147483647) ∧ (426567943 < 2147483647 ∧ 1413532714 < 2147483647); omega) canonical22 (by rfl)
#print axioms add22
theorem mul21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 351056699#u32 1258656308#u32 161645433#u32 1395346597#u32) (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32)=ok (q 1766294252#u32 1719536598#u32 1368899502#u32 1141940472#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (351056699 < 2147483647 ∧ 1258656308 < 2147483647) ∧ (161645433 < 2147483647 ∧ 1395346597 < 2147483647); omega) (by change (1817229702 < 2147483647 ∧ 1607494202 < 2147483647) ∧ (2141385593 < 2147483647 ∧ 540773558 < 2147483647); omega) (by rfl)
#print axioms mul21
theorem add21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1766294252#u32 1719536598#u32 1368899502#u32 1141940472#u32) c21=ok (q 412442857#u32 2077742917#u32 1102709846#u32 725887979#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1766294252 < 2147483647 ∧ 1719536598 < 2147483647) ∧ (1368899502 < 2147483647 ∧ 1141940472 < 2147483647); omega) canonical21 (by rfl)
#print axioms add21
theorem mul20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 412442857#u32 2077742917#u32 1102709846#u32 725887979#u32) (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32)=ok (q 624213524#u32 1955501125#u32 508864070#u32 2014671515#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (412442857 < 2147483647 ∧ 2077742917 < 2147483647) ∧ (1102709846 < 2147483647 ∧ 725887979 < 2147483647); omega) (by change (1817229702 < 2147483647 ∧ 1607494202 < 2147483647) ∧ (2141385593 < 2147483647 ∧ 540773558 < 2147483647); omega) (by rfl)
#print axioms mul20
theorem add20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 624213524#u32 1955501125#u32 508864070#u32 2014671515#u32) c20=ok (q 33307805#u32 1008476059#u32 682597306#u32 133127984#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (624213524 < 2147483647 ∧ 1955501125 < 2147483647) ∧ (508864070 < 2147483647 ∧ 2014671515 < 2147483647); omega) canonical20 (by rfl)
#print axioms add20
theorem mul19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 33307805#u32 1008476059#u32 682597306#u32 133127984#u32) (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32)=ok (q 2095135192#u32 1891889590#u32 710932893#u32 1914620714#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (33307805 < 2147483647 ∧ 1008476059 < 2147483647) ∧ (682597306 < 2147483647 ∧ 133127984 < 2147483647); omega) (by change (1817229702 < 2147483647 ∧ 1607494202 < 2147483647) ∧ (2141385593 < 2147483647 ∧ 540773558 < 2147483647); omega) (by rfl)
#print axioms mul19
theorem add19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2095135192#u32 1891889590#u32 710932893#u32 1914620714#u32) c19=ok (q 1955668582#u32 1586392758#u32 1988885763#u32 1838472278#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2095135192 < 2147483647 ∧ 1891889590 < 2147483647) ∧ (710932893 < 2147483647 ∧ 1914620714 < 2147483647); omega) canonical19 (by rfl)
#print axioms add19
theorem mul18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1955668582#u32 1586392758#u32 1988885763#u32 1838472278#u32) (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32)=ok (q 760655371#u32 1252686967#u32 1828368024#u32 1847670085#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1955668582 < 2147483647 ∧ 1586392758 < 2147483647) ∧ (1988885763 < 2147483647 ∧ 1838472278 < 2147483647); omega) (by change (1817229702 < 2147483647 ∧ 1607494202 < 2147483647) ∧ (2141385593 < 2147483647 ∧ 540773558 < 2147483647); omega) (by rfl)
#print axioms mul18
theorem add18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 760655371#u32 1252686967#u32 1828368024#u32 1847670085#u32) c18=ok (q 957676970#u32 1139700881#u32 320614645#u32 1360639543#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (760655371 < 2147483647 ∧ 1252686967 < 2147483647) ∧ (1828368024 < 2147483647 ∧ 1847670085 < 2147483647); omega) canonical18 (by rfl)
#print axioms add18
theorem mul17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 957676970#u32 1139700881#u32 320614645#u32 1360639543#u32) (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32)=ok (q 1067379739#u32 253694666#u32 463123057#u32 1913091473#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (957676970 < 2147483647 ∧ 1139700881 < 2147483647) ∧ (320614645 < 2147483647 ∧ 1360639543 < 2147483647); omega) (by change (1817229702 < 2147483647 ∧ 1607494202 < 2147483647) ∧ (2141385593 < 2147483647 ∧ 540773558 < 2147483647); omega) (by rfl)
#print axioms mul17
theorem add17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1067379739#u32 253694666#u32 463123057#u32 1913091473#u32) c17=ok (q 1384833849#u32 526406137#u32 1477914099#u32 1729161594#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1067379739 < 2147483647 ∧ 253694666 < 2147483647) ∧ (463123057 < 2147483647 ∧ 1913091473 < 2147483647); omega) canonical17 (by rfl)
#print axioms add17
theorem mul16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1384833849#u32 526406137#u32 1477914099#u32 1729161594#u32) (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32)=ok (q 1601104367#u32 148443686#u32 455557110#u32 1102102897#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1384833849 < 2147483647 ∧ 526406137 < 2147483647) ∧ (1477914099 < 2147483647 ∧ 1729161594 < 2147483647); omega) (by change (1817229702 < 2147483647 ∧ 1607494202 < 2147483647) ∧ (2141385593 < 2147483647 ∧ 540773558 < 2147483647); omega) (by rfl)
#print axioms mul16
theorem add16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1601104367#u32 148443686#u32 455557110#u32 1102102897#u32) c16=ok (q 634705571#u32 1807097113#u32 2036187869#u32 1430368182#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1601104367 < 2147483647 ∧ 148443686 < 2147483647) ∧ (455557110 < 2147483647 ∧ 1102102897 < 2147483647); omega) canonical16 (by rfl)
#print axioms add16
theorem mul15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 634705571#u32 1807097113#u32 2036187869#u32 1430368182#u32) (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32)=ok (q 862062991#u32 1905857880#u32 1665474919#u32 1131307833#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (634705571 < 2147483647 ∧ 1807097113 < 2147483647) ∧ (2036187869 < 2147483647 ∧ 1430368182 < 2147483647); omega) (by change (1817229702 < 2147483647 ∧ 1607494202 < 2147483647) ∧ (2141385593 < 2147483647 ∧ 540773558 < 2147483647); omega) (by rfl)
#print axioms mul15
theorem add15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 862062991#u32 1905857880#u32 1665474919#u32 1131307833#u32) c15=ok (q 1842964296#u32 1056588755#u32 816473943#u32 198330592#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (862062991 < 2147483647 ∧ 1905857880 < 2147483647) ∧ (1665474919 < 2147483647 ∧ 1131307833 < 2147483647); omega) canonical15 (by rfl)
#print axioms add15
theorem mul14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1842964296#u32 1056588755#u32 816473943#u32 198330592#u32) (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32)=ok (q 855302475#u32 1734636891#u32 1022891639#u32 9052810#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1842964296 < 2147483647 ∧ 1056588755 < 2147483647) ∧ (816473943 < 2147483647 ∧ 198330592 < 2147483647); omega) (by change (1817229702 < 2147483647 ∧ 1607494202 < 2147483647) ∧ (2141385593 < 2147483647 ∧ 540773558 < 2147483647); omega) (by rfl)
#print axioms mul14
theorem add14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 855302475#u32 1734636891#u32 1022891639#u32 9052810#u32) c14=ok (q 265808631#u32 1129757301#u32 1597192272#u32 66325017#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (855302475 < 2147483647 ∧ 1734636891 < 2147483647) ∧ (1022891639 < 2147483647 ∧ 9052810 < 2147483647); omega) canonical14 (by rfl)
#print axioms add14
def final : Q := (q 265808631#u32 1129757301#u32 1597192272#u32 66325017#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 2#usize 28#usize initial 14#usize final := by
  refine .step (by change 28>0; omega) (JFr_IndexArithmetic.sub 28#usize 27#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32) from rfl) mul27 (show Array.index_usize p 27#usize=ok c27 from rfl) add27 ?_
  refine .step (by change 27>0; omega) (JFr_IndexArithmetic.sub 27#usize 26#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32) from rfl) mul26 (show Array.index_usize p 26#usize=ok c26 from rfl) add26 ?_
  refine .step (by change 26>0; omega) (JFr_IndexArithmetic.sub 26#usize 25#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32) from rfl) mul25 (show Array.index_usize p 25#usize=ok c25 from rfl) add25 ?_
  refine .step (by change 25>0; omega) (JFr_IndexArithmetic.sub 25#usize 24#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32) from rfl) mul24 (show Array.index_usize p 24#usize=ok c24 from rfl) add24 ?_
  refine .step (by change 24>0; omega) (JFr_IndexArithmetic.sub 24#usize 23#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32) from rfl) mul23 (show Array.index_usize p 23#usize=ok c23 from rfl) add23 ?_
  refine .step (by change 23>0; omega) (JFr_IndexArithmetic.sub 23#usize 22#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32) from rfl) mul22 (show Array.index_usize p 22#usize=ok c22 from rfl) add22 ?_
  refine .step (by change 22>0; omega) (JFr_IndexArithmetic.sub 22#usize 21#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32) from rfl) mul21 (show Array.index_usize p 21#usize=ok c21 from rfl) add21 ?_
  refine .step (by change 21>0; omega) (JFr_IndexArithmetic.sub 21#usize 20#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32) from rfl) mul20 (show Array.index_usize p 20#usize=ok c20 from rfl) add20 ?_
  refine .step (by change 20>0; omega) (JFr_IndexArithmetic.sub 20#usize 19#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32) from rfl) mul19 (show Array.index_usize p 19#usize=ok c19 from rfl) add19 ?_
  refine .step (by change 19>0; omega) (JFr_IndexArithmetic.sub 19#usize 18#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32) from rfl) mul18 (show Array.index_usize p 18#usize=ok c18 from rfl) add18 ?_
  refine .step (by change 18>0; omega) (JFr_IndexArithmetic.sub 18#usize 17#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32) from rfl) mul17 (show Array.index_usize p 17#usize=ok c17 from rfl) add17 ?_
  refine .step (by change 17>0; omega) (JFr_IndexArithmetic.sub 17#usize 16#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32) from rfl) mul16 (show Array.index_usize p 16#usize=ok c16 from rfl) add16 ?_
  refine .step (by change 16>0; omega) (JFr_IndexArithmetic.sub 16#usize 15#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32) from rfl) mul15 (show Array.index_usize p 15#usize=ok c15 from rfl) add15 ?_
  refine .step (by change 15>0; omega) (JFr_IndexArithmetic.sub 15#usize 14#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1817229702#u32 1607494202#u32 2141385593#u32 540773558#u32) from rfl) mul14 (show Array.index_usize p 14#usize=ok c14 from rfl) add14 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner02_0
