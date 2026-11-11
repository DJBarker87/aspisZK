import NDO_JFr_Data00
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner00_0
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data00
def initial : Q := (q 0#u32 0#u32 0#u32 0#u32)
theorem mul27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 0#u32 0#u32 0#u32 0#u32) (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32)=ok (q 0#u32 0#u32 0#u32 0#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) (by change (481946492 < 2147483647 ∧ 959095368 < 2147483647) ∧ (2134045306 < 2147483647 ∧ 1739942601 < 2147483647); omega) (by rfl)
#print axioms mul27
theorem add27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 0#u32 0#u32 0#u32 0#u32) c27=ok (q 571316324#u32 1160853294#u32 1300352358#u32 2094668863#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) canonical27 (by rfl)
#print axioms add27
theorem mul26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 571316324#u32 1160853294#u32 1300352358#u32 2094668863#u32) (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32)=ok (q 921368232#u32 1581306430#u32 2047588918#u32 1751313250#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (571316324 < 2147483647 ∧ 1160853294 < 2147483647) ∧ (1300352358 < 2147483647 ∧ 2094668863 < 2147483647); omega) (by change (481946492 < 2147483647 ∧ 959095368 < 2147483647) ∧ (2134045306 < 2147483647 ∧ 1739942601 < 2147483647); omega) (by rfl)
#print axioms mul26
theorem add26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 921368232#u32 1581306430#u32 2047588918#u32 1751313250#u32) c26=ok (q 1651216765#u32 659295585#u32 1183667561#u32 305219652#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (921368232 < 2147483647 ∧ 1581306430 < 2147483647) ∧ (2047588918 < 2147483647 ∧ 1751313250 < 2147483647); omega) canonical26 (by rfl)
#print axioms add26
theorem mul25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1651216765#u32 659295585#u32 1183667561#u32 305219652#u32) (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32)=ok (q 2003458471#u32 1088626123#u32 1258987571#u32 1353498347#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1651216765 < 2147483647 ∧ 659295585 < 2147483647) ∧ (1183667561 < 2147483647 ∧ 305219652 < 2147483647); omega) (by change (481946492 < 2147483647 ∧ 959095368 < 2147483647) ∧ (2134045306 < 2147483647 ∧ 1739942601 < 2147483647); omega) (by rfl)
#print axioms mul25
theorem add25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2003458471#u32 1088626123#u32 1258987571#u32 1353498347#u32) c25=ok (q 820726796#u32 1417639633#u32 60632818#u32 483829611#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2003458471 < 2147483647 ∧ 1088626123 < 2147483647) ∧ (1258987571 < 2147483647 ∧ 1353498347 < 2147483647); omega) canonical25 (by rfl)
#print axioms add25
theorem mul24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 820726796#u32 1417639633#u32 60632818#u32 483829611#u32) (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32)=ok (q 1642534626#u32 959405695#u32 1722082043#u32 1592023392#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (820726796 < 2147483647 ∧ 1417639633 < 2147483647) ∧ (60632818 < 2147483647 ∧ 483829611 < 2147483647); omega) (by change (481946492 < 2147483647 ∧ 959095368 < 2147483647) ∧ (2134045306 < 2147483647 ∧ 1739942601 < 2147483647); omega) (by rfl)
#print axioms mul24
theorem add24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1642534626#u32 959405695#u32 1722082043#u32 1592023392#u32) c24=ok (q 817394359#u32 1756919017#u32 649318016#u32 1751735830#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1642534626 < 2147483647 ∧ 959405695 < 2147483647) ∧ (1722082043 < 2147483647 ∧ 1592023392 < 2147483647); omega) canonical24 (by rfl)
#print axioms add24
theorem mul23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 817394359#u32 1756919017#u32 649318016#u32 1751735830#u32) (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32)=ok (q 457299140#u32 1372565988#u32 555412831#u32 108101778#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (817394359 < 2147483647 ∧ 1756919017 < 2147483647) ∧ (649318016 < 2147483647 ∧ 1751735830 < 2147483647); omega) (by change (481946492 < 2147483647 ∧ 959095368 < 2147483647) ∧ (2134045306 < 2147483647 ∧ 1739942601 < 2147483647); omega) (by rfl)
#print axioms mul23
theorem add23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 457299140#u32 1372565988#u32 555412831#u32 108101778#u32) c23=ok (q 1424626811#u32 147986399#u32 435293728#u32 2083532459#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (457299140 < 2147483647 ∧ 1372565988 < 2147483647) ∧ (555412831 < 2147483647 ∧ 108101778 < 2147483647); omega) canonical23 (by rfl)
#print axioms add23
theorem mul22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1424626811#u32 147986399#u32 435293728#u32 2083532459#u32) (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32)=ok (q 689537704#u32 1537437259#u32 775496582#u32 1485112676#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1424626811 < 2147483647 ∧ 147986399 < 2147483647) ∧ (435293728 < 2147483647 ∧ 2083532459 < 2147483647); omega) (by change (481946492 < 2147483647 ∧ 959095368 < 2147483647) ∧ (2134045306 < 2147483647 ∧ 1739942601 < 2147483647); omega) (by rfl)
#print axioms mul22
theorem add22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 689537704#u32 1537437259#u32 775496582#u32 1485112676#u32) c22=ok (q 1151144815#u32 1206545572#u32 309390858#u32 2248372#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (689537704 < 2147483647 ∧ 1537437259 < 2147483647) ∧ (775496582 < 2147483647 ∧ 1485112676 < 2147483647); omega) canonical22 (by rfl)
#print axioms add22
theorem mul21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1151144815#u32 1206545572#u32 309390858#u32 2248372#u32) (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32)=ok (q 956115222#u32 84619119#u32 1063005901#u32 1486595683#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1151144815 < 2147483647 ∧ 1206545572 < 2147483647) ∧ (309390858 < 2147483647 ∧ 2248372 < 2147483647); omega) (by change (481946492 < 2147483647 ∧ 959095368 < 2147483647) ∧ (2134045306 < 2147483647 ∧ 1739942601 < 2147483647); omega) (by rfl)
#print axioms mul21
theorem add21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 956115222#u32 84619119#u32 1063005901#u32 1486595683#u32) c21=ok (q 229642842#u32 879594630#u32 1532364544#u32 428013052#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (956115222 < 2147483647 ∧ 84619119 < 2147483647) ∧ (1063005901 < 2147483647 ∧ 1486595683 < 2147483647); omega) canonical21 (by rfl)
#print axioms add21
theorem mul20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 229642842#u32 879594630#u32 1532364544#u32 428013052#u32) (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32)=ok (q 2094902546#u32 1517533079#u32 358684938#u32 1751111283#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (229642842 < 2147483647 ∧ 879594630 < 2147483647) ∧ (1532364544 < 2147483647 ∧ 428013052 < 2147483647); omega) (by change (481946492 < 2147483647 ∧ 959095368 < 2147483647) ∧ (2134045306 < 2147483647 ∧ 1739942601 < 2147483647); omega) (by rfl)
#print axioms mul20
theorem add20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2094902546#u32 1517533079#u32 358684938#u32 1751111283#u32) c20=ok (q 633303443#u32 1964808519#u32 1806383675#u32 1236032327#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2094902546 < 2147483647 ∧ 1517533079 < 2147483647) ∧ (358684938 < 2147483647 ∧ 1751111283 < 2147483647); omega) canonical20 (by rfl)
#print axioms add20
theorem mul19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 633303443#u32 1964808519#u32 1806383675#u32 1236032327#u32) (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32)=ok (q 1409258341#u32 520135300#u32 1614258713#u32 612674605#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (633303443 < 2147483647 ∧ 1964808519 < 2147483647) ∧ (1806383675 < 2147483647 ∧ 1236032327 < 2147483647); omega) (by change (481946492 < 2147483647 ∧ 959095368 < 2147483647) ∧ (2134045306 < 2147483647 ∧ 1739942601 < 2147483647); omega) (by rfl)
#print axioms mul19
theorem add19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1409258341#u32 520135300#u32 1614258713#u32 612674605#u32) c19=ok (q 1572493376#u32 228910128#u32 81143278#u32 2097948187#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1409258341 < 2147483647 ∧ 520135300 < 2147483647) ∧ (1614258713 < 2147483647 ∧ 612674605 < 2147483647); omega) canonical19 (by rfl)
#print axioms add19
theorem mul18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1572493376#u32 228910128#u32 81143278#u32 2097948187#u32) (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32)=ok (q 761368832#u32 234119543#u32 96373619#u32 1814332608#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1572493376 < 2147483647 ∧ 228910128 < 2147483647) ∧ (81143278 < 2147483647 ∧ 2097948187 < 2147483647); omega) (by change (481946492 < 2147483647 ∧ 959095368 < 2147483647) ∧ (2134045306 < 2147483647 ∧ 1739942601 < 2147483647); omega) (by rfl)
#print axioms mul18
theorem add18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 761368832#u32 234119543#u32 96373619#u32 1814332608#u32) c18=ok (q 73483268#u32 629307667#u32 1984669206#u32 1066394605#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (761368832 < 2147483647 ∧ 234119543 < 2147483647) ∧ (96373619 < 2147483647 ∧ 1814332608 < 2147483647); omega) canonical18 (by rfl)
#print axioms add18
theorem mul17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 73483268#u32 629307667#u32 1984669206#u32 1066394605#u32) (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32)=ok (q 992612196#u32 1746417578#u32 200674444#u32 1791889351#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (73483268 < 2147483647 ∧ 629307667 < 2147483647) ∧ (1984669206 < 2147483647 ∧ 1066394605 < 2147483647); omega) (by change (481946492 < 2147483647 ∧ 959095368 < 2147483647) ∧ (2134045306 < 2147483647 ∧ 1739942601 < 2147483647); omega) (by rfl)
#print axioms mul17
theorem add17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 992612196#u32 1746417578#u32 200674444#u32 1791889351#u32) c17=ok (q 114321157#u32 1137138425#u32 899666773#u32 1490285884#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (992612196 < 2147483647 ∧ 1746417578 < 2147483647) ∧ (200674444 < 2147483647 ∧ 1791889351 < 2147483647); omega) canonical17 (by rfl)
#print axioms add17
theorem mul16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 114321157#u32 1137138425#u32 899666773#u32 1490285884#u32) (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32)=ok (q 343720487#u32 924385946#u32 1255710607#u32 838686289#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (114321157 < 2147483647 ∧ 1137138425 < 2147483647) ∧ (899666773 < 2147483647 ∧ 1490285884 < 2147483647); omega) (by change (481946492 < 2147483647 ∧ 959095368 < 2147483647) ∧ (2134045306 < 2147483647 ∧ 1739942601 < 2147483647); omega) (by rfl)
#print axioms mul16
theorem add16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 343720487#u32 924385946#u32 1255710607#u32 838686289#u32) c16=ok (q 387599075#u32 1657792312#u32 1449030079#u32 2134552203#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (343720487 < 2147483647 ∧ 924385946 < 2147483647) ∧ (1255710607 < 2147483647 ∧ 838686289 < 2147483647); omega) canonical16 (by rfl)
#print axioms add16
theorem mul15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 387599075#u32 1657792312#u32 1449030079#u32 2134552203#u32) (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32)=ok (q 1655908226#u32 227129265#u32 754546042#u32 717284274#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (387599075 < 2147483647 ∧ 1657792312 < 2147483647) ∧ (1449030079 < 2147483647 ∧ 2134552203 < 2147483647); omega) (by change (481946492 < 2147483647 ∧ 959095368 < 2147483647) ∧ (2134045306 < 2147483647 ∧ 1739942601 < 2147483647); omega) (by rfl)
#print axioms mul15
theorem add15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1655908226#u32 227129265#u32 754546042#u32 717284274#u32) c15=ok (q 48662006#u32 1071826001#u32 727706187#u32 1458956316#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1655908226 < 2147483647 ∧ 227129265 < 2147483647) ∧ (754546042 < 2147483647 ∧ 717284274 < 2147483647); omega) canonical15 (by rfl)
#print axioms add15
theorem mul14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 48662006#u32 1071826001#u32 727706187#u32 1458956316#u32) (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32)=ok (q 725634381#u32 2024245442#u32 1879861500#u32 1519121139#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (48662006 < 2147483647 ∧ 1071826001 < 2147483647) ∧ (727706187 < 2147483647 ∧ 1458956316 < 2147483647); omega) (by change (481946492 < 2147483647 ∧ 959095368 < 2147483647) ∧ (2134045306 < 2147483647 ∧ 1739942601 < 2147483647); omega) (by rfl)
#print axioms mul14
theorem add14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 725634381#u32 2024245442#u32 1879861500#u32 1519121139#u32) c14=ok (q 484123196#u32 1780186450#u32 1612679921#u32 1127012705#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (725634381 < 2147483647 ∧ 2024245442 < 2147483647) ∧ (1879861500 < 2147483647 ∧ 1519121139 < 2147483647); omega) canonical14 (by rfl)
#print axioms add14
def final : Q := (q 484123196#u32 1780186450#u32 1612679921#u32 1127012705#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 0#usize 28#usize initial 14#usize final := by
  refine .step (by change 28>0; omega) (JFr_IndexArithmetic.sub 28#usize 27#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32) from rfl) mul27 (show Array.index_usize p 27#usize=ok c27 from rfl) add27 ?_
  refine .step (by change 27>0; omega) (JFr_IndexArithmetic.sub 27#usize 26#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32) from rfl) mul26 (show Array.index_usize p 26#usize=ok c26 from rfl) add26 ?_
  refine .step (by change 26>0; omega) (JFr_IndexArithmetic.sub 26#usize 25#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32) from rfl) mul25 (show Array.index_usize p 25#usize=ok c25 from rfl) add25 ?_
  refine .step (by change 25>0; omega) (JFr_IndexArithmetic.sub 25#usize 24#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32) from rfl) mul24 (show Array.index_usize p 24#usize=ok c24 from rfl) add24 ?_
  refine .step (by change 24>0; omega) (JFr_IndexArithmetic.sub 24#usize 23#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32) from rfl) mul23 (show Array.index_usize p 23#usize=ok c23 from rfl) add23 ?_
  refine .step (by change 23>0; omega) (JFr_IndexArithmetic.sub 23#usize 22#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32) from rfl) mul22 (show Array.index_usize p 22#usize=ok c22 from rfl) add22 ?_
  refine .step (by change 22>0; omega) (JFr_IndexArithmetic.sub 22#usize 21#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32) from rfl) mul21 (show Array.index_usize p 21#usize=ok c21 from rfl) add21 ?_
  refine .step (by change 21>0; omega) (JFr_IndexArithmetic.sub 21#usize 20#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32) from rfl) mul20 (show Array.index_usize p 20#usize=ok c20 from rfl) add20 ?_
  refine .step (by change 20>0; omega) (JFr_IndexArithmetic.sub 20#usize 19#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32) from rfl) mul19 (show Array.index_usize p 19#usize=ok c19 from rfl) add19 ?_
  refine .step (by change 19>0; omega) (JFr_IndexArithmetic.sub 19#usize 18#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32) from rfl) mul18 (show Array.index_usize p 18#usize=ok c18 from rfl) add18 ?_
  refine .step (by change 18>0; omega) (JFr_IndexArithmetic.sub 18#usize 17#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32) from rfl) mul17 (show Array.index_usize p 17#usize=ok c17 from rfl) add17 ?_
  refine .step (by change 17>0; omega) (JFr_IndexArithmetic.sub 17#usize 16#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32) from rfl) mul16 (show Array.index_usize p 16#usize=ok c16 from rfl) add16 ?_
  refine .step (by change 16>0; omega) (JFr_IndexArithmetic.sub 16#usize 15#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32) from rfl) mul15 (show Array.index_usize p 15#usize=ok c15 from rfl) add15 ?_
  refine .step (by change 15>0; omega) (JFr_IndexArithmetic.sub 15#usize 14#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32) from rfl) mul14 (show Array.index_usize p 14#usize=ok c14 from rfl) add14 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner00_0
