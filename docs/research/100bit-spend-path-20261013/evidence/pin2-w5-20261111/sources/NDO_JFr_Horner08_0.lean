import NDO_JFr_Data08
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner08_0
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data08
def initial : Q := (q 0#u32 0#u32 0#u32 0#u32)
theorem mul27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 0#u32 0#u32 0#u32 0#u32) (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32)=ok (q 0#u32 0#u32 0#u32 0#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) (by change (124721160 < 2147483647 ∧ 1463026064 < 2147483647) ∧ (316880895 < 2147483647 ∧ 1559203092 < 2147483647); omega) (by rfl)
#print axioms mul27
theorem add27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 0#u32 0#u32 0#u32 0#u32) c27=ok (q 1706825806#u32 1554064316#u32 327575599#u32 1396424252#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) canonical27 (by rfl)
#print axioms add27
theorem mul26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1706825806#u32 1554064316#u32 327575599#u32 1396424252#u32) (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32)=ok (q 1490916800#u32 2011059585#u32 150260454#u32 1908190538#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1706825806 < 2147483647 ∧ 1554064316 < 2147483647) ∧ (327575599 < 2147483647 ∧ 1396424252 < 2147483647); omega) (by change (124721160 < 2147483647 ∧ 1463026064 < 2147483647) ∧ (316880895 < 2147483647 ∧ 1559203092 < 2147483647); omega) (by rfl)
#print axioms mul26
theorem add26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1490916800#u32 2011059585#u32 150260454#u32 1908190538#u32) c26=ok (q 34172913#u32 558826140#u32 521692148#u32 421373368#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1490916800 < 2147483647 ∧ 2011059585 < 2147483647) ∧ (150260454 < 2147483647 ∧ 1908190538 < 2147483647); omega) canonical26 (by rfl)
#print axioms add26
theorem mul25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 34172913#u32 558826140#u32 521692148#u32 421373368#u32) (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32)=ok (q 1249234225#u32 2049222775#u32 1391526071#u32 1223600976#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (34172913 < 2147483647 ∧ 558826140 < 2147483647) ∧ (521692148 < 2147483647 ∧ 421373368 < 2147483647); omega) (by change (124721160 < 2147483647 ∧ 1463026064 < 2147483647) ∧ (316880895 < 2147483647 ∧ 1559203092 < 2147483647); omega) (by rfl)
#print axioms mul25
theorem add25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1249234225#u32 2049222775#u32 1391526071#u32 1223600976#u32) c25=ok (q 1503262400#u32 827267986#u32 1491040926#u32 176917651#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1249234225 < 2147483647 ∧ 2049222775 < 2147483647) ∧ (1391526071 < 2147483647 ∧ 1223600976 < 2147483647); omega) canonical25 (by rfl)
#print axioms add25
theorem mul24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1503262400#u32 827267986#u32 1491040926#u32 176917651#u32) (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32)=ok (q 1598691193#u32 873369958#u32 544162044#u32 1550477856#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1503262400 < 2147483647 ∧ 827267986 < 2147483647) ∧ (1491040926 < 2147483647 ∧ 176917651 < 2147483647); omega) (by change (124721160 < 2147483647 ∧ 1463026064 < 2147483647) ∧ (316880895 < 2147483647 ∧ 1559203092 < 2147483647); omega) (by rfl)
#print axioms mul24
theorem add24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1598691193#u32 873369958#u32 544162044#u32 1550477856#u32) c24=ok (q 1505215238#u32 2143445945#u32 1219348055#u32 23620572#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1598691193 < 2147483647 ∧ 873369958 < 2147483647) ∧ (544162044 < 2147483647 ∧ 1550477856 < 2147483647); omega) canonical24 (by rfl)
#print axioms add24
theorem mul23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1505215238#u32 2143445945#u32 1219348055#u32 23620572#u32) (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32)=ok (q 1952930358#u32 1924196822#u32 1444152074#u32 1980052837#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1505215238 < 2147483647 ∧ 2143445945 < 2147483647) ∧ (1219348055 < 2147483647 ∧ 23620572 < 2147483647); omega) (by change (124721160 < 2147483647 ∧ 1463026064 < 2147483647) ∧ (316880895 < 2147483647 ∧ 1559203092 < 2147483647); omega) (by rfl)
#print axioms mul23
theorem add23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1952930358#u32 1924196822#u32 1444152074#u32 1980052837#u32) c23=ok (q 554495759#u32 1693071419#u32 2101318549#u32 781061143#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1952930358 < 2147483647 ∧ 1924196822 < 2147483647) ∧ (1444152074 < 2147483647 ∧ 1980052837 < 2147483647); omega) canonical23 (by rfl)
#print axioms add23
theorem mul22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 554495759#u32 1693071419#u32 2101318549#u32 781061143#u32) (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32)=ok (q 857330734#u32 1152809463#u32 891954768#u32 359940494#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (554495759 < 2147483647 ∧ 1693071419 < 2147483647) ∧ (2101318549 < 2147483647 ∧ 781061143 < 2147483647); omega) (by change (124721160 < 2147483647 ∧ 1463026064 < 2147483647) ∧ (316880895 < 2147483647 ∧ 1559203092 < 2147483647); omega) (by rfl)
#print axioms mul22
theorem add22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 857330734#u32 1152809463#u32 891954768#u32 359940494#u32) c22=ok (q 888862825#u32 660701224#u32 507248816#u32 968350504#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (857330734 < 2147483647 ∧ 1152809463 < 2147483647) ∧ (891954768 < 2147483647 ∧ 359940494 < 2147483647); omega) canonical22 (by rfl)
#print axioms add22
theorem mul21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 888862825#u32 660701224#u32 507248816#u32 968350504#u32) (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32)=ok (q 623015722#u32 1349754458#u32 879605370#u32 1123125370#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (888862825 < 2147483647 ∧ 660701224 < 2147483647) ∧ (507248816 < 2147483647 ∧ 968350504 < 2147483647); omega) (by change (124721160 < 2147483647 ∧ 1463026064 < 2147483647) ∧ (316880895 < 2147483647 ∧ 1559203092 < 2147483647); omega) (by rfl)
#print axioms mul21
theorem add21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 623015722#u32 1349754458#u32 879605370#u32 1123125370#u32) c21=ok (q 319427171#u32 194556414#u32 1484946539#u32 1129881182#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (623015722 < 2147483647 ∧ 1349754458 < 2147483647) ∧ (879605370 < 2147483647 ∧ 1123125370 < 2147483647); omega) canonical21 (by rfl)
#print axioms add21
theorem mul20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 319427171#u32 194556414#u32 1484946539#u32 1129881182#u32) (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32)=ok (q 691358862#u32 1574613280#u32 1206214477#u32 933552021#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (319427171 < 2147483647 ∧ 194556414 < 2147483647) ∧ (1484946539 < 2147483647 ∧ 1129881182 < 2147483647); omega) (by change (124721160 < 2147483647 ∧ 1463026064 < 2147483647) ∧ (316880895 < 2147483647 ∧ 1559203092 < 2147483647); omega) (by rfl)
#print axioms mul20
theorem add20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 691358862#u32 1574613280#u32 1206214477#u32 933552021#u32) c20=ok (q 648774502#u32 1353414772#u32 573436145#u32 1643500303#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (691358862 < 2147483647 ∧ 1574613280 < 2147483647) ∧ (1206214477 < 2147483647 ∧ 933552021 < 2147483647); omega) canonical20 (by rfl)
#print axioms add20
theorem mul19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 648774502#u32 1353414772#u32 573436145#u32 1643500303#u32) (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32)=ok (q 738387395#u32 897889585#u32 473738868#u32 104029219#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (648774502 < 2147483647 ∧ 1353414772 < 2147483647) ∧ (573436145 < 2147483647 ∧ 1643500303 < 2147483647); omega) (by change (124721160 < 2147483647 ∧ 1463026064 < 2147483647) ∧ (316880895 < 2147483647 ∧ 1559203092 < 2147483647); omega) (by rfl)
#print axioms mul19
theorem add19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 738387395#u32 897889585#u32 473738868#u32 104029219#u32) c19=ok (q 838020629#u32 181457582#u32 1590620440#u32 1907049776#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (738387395 < 2147483647 ∧ 897889585 < 2147483647) ∧ (473738868 < 2147483647 ∧ 104029219 < 2147483647); omega) canonical19 (by rfl)
#print axioms add19
theorem mul18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 838020629#u32 181457582#u32 1590620440#u32 1907049776#u32) (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32)=ok (q 2074823369#u32 419231352#u32 245847772#u32 897109667#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (838020629 < 2147483647 ∧ 181457582 < 2147483647) ∧ (1590620440 < 2147483647 ∧ 1907049776 < 2147483647); omega) (by change (124721160 < 2147483647 ∧ 1463026064 < 2147483647) ∧ (316880895 < 2147483647 ∧ 1559203092 < 2147483647); omega) (by rfl)
#print axioms mul18
theorem add18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2074823369#u32 419231352#u32 245847772#u32 897109667#u32) c18=ok (q 825990957#u32 142523428#u32 385041342#u32 1509661252#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2074823369 < 2147483647 ∧ 419231352 < 2147483647) ∧ (245847772 < 2147483647 ∧ 897109667 < 2147483647); omega) canonical18 (by rfl)
#print axioms add18
theorem mul17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 825990957#u32 142523428#u32 385041342#u32 1509661252#u32) (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32)=ok (q 1927970676#u32 2117831783#u32 1826621166#u32 323605240#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (825990957 < 2147483647 ∧ 142523428 < 2147483647) ∧ (385041342 < 2147483647 ∧ 1509661252 < 2147483647); omega) (by change (124721160 < 2147483647 ∧ 1463026064 < 2147483647) ∧ (316880895 < 2147483647 ∧ 1559203092 < 2147483647); omega) (by rfl)
#print axioms mul17
theorem add17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1927970676#u32 2117831783#u32 1826621166#u32 323605240#u32) c17=ok (q 870006834#u32 1490678503#u32 2011134871#u32 993770855#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1927970676 < 2147483647 ∧ 2117831783 < 2147483647) ∧ (1826621166 < 2147483647 ∧ 323605240 < 2147483647); omega) canonical17 (by rfl)
#print axioms add17
theorem mul16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 870006834#u32 1490678503#u32 2011134871#u32 993770855#u32) (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32)=ok (q 1223667265#u32 959276147#u32 1972574450#u32 1347165165#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (870006834 < 2147483647 ∧ 1490678503 < 2147483647) ∧ (2011134871 < 2147483647 ∧ 993770855 < 2147483647); omega) (by change (124721160 < 2147483647 ∧ 1463026064 < 2147483647) ∧ (316880895 < 2147483647 ∧ 1559203092 < 2147483647); omega) (by rfl)
#print axioms mul16
theorem add16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1223667265#u32 959276147#u32 1972574450#u32 1347165165#u32) c16=ok (q 1614554997#u32 1239981571#u32 947901985#u32 1577550138#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1223667265 < 2147483647 ∧ 959276147 < 2147483647) ∧ (1972574450 < 2147483647 ∧ 1347165165 < 2147483647); omega) canonical16 (by rfl)
#print axioms add16
theorem mul15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1614554997#u32 1239981571#u32 947901985#u32 1577550138#u32) (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32)=ok (q 1722862439#u32 1532646299#u32 985976784#u32 816298683#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1614554997 < 2147483647 ∧ 1239981571 < 2147483647) ∧ (947901985 < 2147483647 ∧ 1577550138 < 2147483647); omega) (by change (124721160 < 2147483647 ∧ 1463026064 < 2147483647) ∧ (316880895 < 2147483647 ∧ 1559203092 < 2147483647); omega) (by rfl)
#print axioms mul15
theorem add15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1722862439#u32 1532646299#u32 985976784#u32 816298683#u32) c15=ok (q 1797441682#u32 337237251#u32 86423161#u32 1804157193#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1722862439 < 2147483647 ∧ 1532646299 < 2147483647) ∧ (985976784 < 2147483647 ∧ 816298683 < 2147483647); omega) canonical15 (by rfl)
#print axioms add15
theorem mul14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1797441682#u32 337237251#u32 86423161#u32 1804157193#u32) (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32)=ok (q 1334956327#u32 596856555#u32 885901420#u32 746780179#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1797441682 < 2147483647 ∧ 337237251 < 2147483647) ∧ (86423161 < 2147483647 ∧ 1804157193 < 2147483647); omega) (by change (124721160 < 2147483647 ∧ 1463026064 < 2147483647) ∧ (316880895 < 2147483647 ∧ 1559203092 < 2147483647); omega) (by rfl)
#print axioms mul14
theorem add14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1334956327#u32 596856555#u32 885901420#u32 746780179#u32) c14=ok (q 2112930430#u32 1994933690#u32 877632083#u32 1341230312#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1334956327 < 2147483647 ∧ 596856555 < 2147483647) ∧ (885901420 < 2147483647 ∧ 746780179 < 2147483647); omega) canonical14 (by rfl)
#print axioms add14
def final : Q := (q 2112930430#u32 1994933690#u32 877632083#u32 1341230312#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 8#usize 28#usize initial 14#usize final := by
  refine .step (by change 28>0; omega) (JFr_IndexArithmetic.sub 28#usize 27#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32) from rfl) mul27 (show Array.index_usize p 27#usize=ok c27 from rfl) add27 ?_
  refine .step (by change 27>0; omega) (JFr_IndexArithmetic.sub 27#usize 26#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32) from rfl) mul26 (show Array.index_usize p 26#usize=ok c26 from rfl) add26 ?_
  refine .step (by change 26>0; omega) (JFr_IndexArithmetic.sub 26#usize 25#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32) from rfl) mul25 (show Array.index_usize p 25#usize=ok c25 from rfl) add25 ?_
  refine .step (by change 25>0; omega) (JFr_IndexArithmetic.sub 25#usize 24#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32) from rfl) mul24 (show Array.index_usize p 24#usize=ok c24 from rfl) add24 ?_
  refine .step (by change 24>0; omega) (JFr_IndexArithmetic.sub 24#usize 23#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32) from rfl) mul23 (show Array.index_usize p 23#usize=ok c23 from rfl) add23 ?_
  refine .step (by change 23>0; omega) (JFr_IndexArithmetic.sub 23#usize 22#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32) from rfl) mul22 (show Array.index_usize p 22#usize=ok c22 from rfl) add22 ?_
  refine .step (by change 22>0; omega) (JFr_IndexArithmetic.sub 22#usize 21#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32) from rfl) mul21 (show Array.index_usize p 21#usize=ok c21 from rfl) add21 ?_
  refine .step (by change 21>0; omega) (JFr_IndexArithmetic.sub 21#usize 20#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32) from rfl) mul20 (show Array.index_usize p 20#usize=ok c20 from rfl) add20 ?_
  refine .step (by change 20>0; omega) (JFr_IndexArithmetic.sub 20#usize 19#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32) from rfl) mul19 (show Array.index_usize p 19#usize=ok c19 from rfl) add19 ?_
  refine .step (by change 19>0; omega) (JFr_IndexArithmetic.sub 19#usize 18#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32) from rfl) mul18 (show Array.index_usize p 18#usize=ok c18 from rfl) add18 ?_
  refine .step (by change 18>0; omega) (JFr_IndexArithmetic.sub 18#usize 17#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32) from rfl) mul17 (show Array.index_usize p 17#usize=ok c17 from rfl) add17 ?_
  refine .step (by change 17>0; omega) (JFr_IndexArithmetic.sub 17#usize 16#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32) from rfl) mul16 (show Array.index_usize p 16#usize=ok c16 from rfl) add16 ?_
  refine .step (by change 16>0; omega) (JFr_IndexArithmetic.sub 16#usize 15#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32) from rfl) mul15 (show Array.index_usize p 15#usize=ok c15 from rfl) add15 ?_
  refine .step (by change 15>0; omega) (JFr_IndexArithmetic.sub 15#usize 14#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32) from rfl) mul14 (show Array.index_usize p 14#usize=ok c14 from rfl) add14 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner08_0
