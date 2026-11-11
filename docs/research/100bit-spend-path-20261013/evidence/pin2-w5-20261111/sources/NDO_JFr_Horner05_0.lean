import NDO_JFr_Data05
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner05_0
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data05
def initial : Q := (q 0#u32 0#u32 0#u32 0#u32)
theorem mul27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 0#u32 0#u32 0#u32 0#u32) (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32)=ok (q 0#u32 0#u32 0#u32 0#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) (by change (1976533199 < 2147483647 ∧ 2142788478 < 2147483647) ∧ (1835806328 < 2147483647 ∧ 1950703221 < 2147483647); omega) (by rfl)
#print axioms mul27
theorem add27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 0#u32 0#u32 0#u32 0#u32) c27=ok (q 548645475#u32 1967904840#u32 391066162#u32 2074674155#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) canonical27 (by rfl)
#print axioms add27
theorem mul26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 548645475#u32 1967904840#u32 391066162#u32 2074674155#u32) (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32)=ok (q 1798166378#u32 911971492#u32 464139404#u32 1419448433#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (548645475 < 2147483647 ∧ 1967904840 < 2147483647) ∧ (391066162 < 2147483647 ∧ 2074674155 < 2147483647); omega) (by change (1976533199 < 2147483647 ∧ 2142788478 < 2147483647) ∧ (1835806328 < 2147483647 ∧ 1950703221 < 2147483647); omega) (by rfl)
#print axioms mul26
theorem add26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1798166378#u32 911971492#u32 464139404#u32 1419448433#u32) c26=ok (q 325977767#u32 378781930#u32 721668098#u32 157288518#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1798166378 < 2147483647 ∧ 911971492 < 2147483647) ∧ (464139404 < 2147483647 ∧ 1419448433 < 2147483647); omega) canonical26 (by rfl)
#print axioms add26
theorem mul25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 325977767#u32 378781930#u32 721668098#u32 157288518#u32) (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32)=ok (q 1785125125#u32 847747950#u32 776548398#u32 1219133784#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (325977767 < 2147483647 ∧ 378781930 < 2147483647) ∧ (721668098 < 2147483647 ∧ 157288518 < 2147483647); omega) (by change (1976533199 < 2147483647 ∧ 2142788478 < 2147483647) ∧ (1835806328 < 2147483647 ∧ 1950703221 < 2147483647); omega) (by rfl)
#print axioms mul25
theorem add25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1785125125#u32 847747950#u32 776548398#u32 1219133784#u32) c25=ok (q 1533996850#u32 723969701#u32 290690014#u32 1464622825#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1785125125 < 2147483647 ∧ 847747950 < 2147483647) ∧ (776548398 < 2147483647 ∧ 1219133784 < 2147483647); omega) canonical25 (by rfl)
#print axioms add25
theorem mul24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1533996850#u32 723969701#u32 290690014#u32 1464622825#u32) (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32)=ok (q 905566356#u32 935535358#u32 1428829928#u32 1841251624#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1533996850 < 2147483647 ∧ 723969701 < 2147483647) ∧ (290690014 < 2147483647 ∧ 1464622825 < 2147483647); omega) (by change (1976533199 < 2147483647 ∧ 2142788478 < 2147483647) ∧ (1835806328 < 2147483647 ∧ 1950703221 < 2147483647); omega) (by rfl)
#print axioms mul24
theorem add24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 905566356#u32 935535358#u32 1428829928#u32 1841251624#u32) c24=ok (q 1619332145#u32 1868136745#u32 1914096134#u32 1348914627#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (905566356 < 2147483647 ∧ 935535358 < 2147483647) ∧ (1428829928 < 2147483647 ∧ 1841251624 < 2147483647); omega) canonical24 (by rfl)
#print axioms add24
theorem mul23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1619332145#u32 1868136745#u32 1914096134#u32 1348914627#u32) (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32)=ok (q 1600819434#u32 1927147610#u32 140679229#u32 2041470764#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1619332145 < 2147483647 ∧ 1868136745 < 2147483647) ∧ (1914096134 < 2147483647 ∧ 1348914627 < 2147483647); omega) (by change (1976533199 < 2147483647 ∧ 2142788478 < 2147483647) ∧ (1835806328 < 2147483647 ∧ 1950703221 < 2147483647); omega) (by rfl)
#print axioms mul23
theorem add23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1600819434#u32 1927147610#u32 140679229#u32 2041470764#u32) c23=ok (q 995081120#u32 1553574691#u32 1128982520#u32 699387058#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1600819434 < 2147483647 ∧ 1927147610 < 2147483647) ∧ (140679229 < 2147483647 ∧ 2041470764 < 2147483647); omega) canonical23 (by rfl)
#print axioms add23
theorem mul22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 995081120#u32 1553574691#u32 1128982520#u32 699387058#u32) (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32)=ok (q 1478374306#u32 598341125#u32 1994316166#u32 2089804700#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (995081120 < 2147483647 ∧ 1553574691 < 2147483647) ∧ (1128982520 < 2147483647 ∧ 699387058 < 2147483647); omega) (by change (1976533199 < 2147483647 ∧ 2142788478 < 2147483647) ∧ (1835806328 < 2147483647 ∧ 1950703221 < 2147483647); omega) (by rfl)
#print axioms mul22
theorem add22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1478374306#u32 598341125#u32 1994316166#u32 2089804700#u32) c22=ok (q 361813017#u32 1069019977#u32 675305069#u32 1091917091#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1478374306 < 2147483647 ∧ 598341125 < 2147483647) ∧ (1994316166 < 2147483647 ∧ 2089804700 < 2147483647); omega) canonical22 (by rfl)
#print axioms add22
theorem mul21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 361813017#u32 1069019977#u32 675305069#u32 1091917091#u32) (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32)=ok (q 828927608#u32 458047844#u32 1804955427#u32 1518741025#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (361813017 < 2147483647 ∧ 1069019977 < 2147483647) ∧ (675305069 < 2147483647 ∧ 1091917091 < 2147483647); omega) (by change (1976533199 < 2147483647 ∧ 2142788478 < 2147483647) ∧ (1835806328 < 2147483647 ∧ 1950703221 < 2147483647); omega) (by rfl)
#print axioms mul21
theorem add21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 828927608#u32 458047844#u32 1804955427#u32 1518741025#u32) c21=ok (q 1304339712#u32 639330840#u32 1829993465#u32 553201865#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (828927608 < 2147483647 ∧ 458047844 < 2147483647) ∧ (1804955427 < 2147483647 ∧ 1518741025 < 2147483647); omega) canonical21 (by rfl)
#print axioms add21
theorem mul20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1304339712#u32 639330840#u32 1829993465#u32 553201865#u32) (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32)=ok (q 1008247216#u32 115515461#u32 604293221#u32 137235728#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1304339712 < 2147483647 ∧ 639330840 < 2147483647) ∧ (1829993465 < 2147483647 ∧ 553201865 < 2147483647); omega) (by change (1976533199 < 2147483647 ∧ 2142788478 < 2147483647) ∧ (1835806328 < 2147483647 ∧ 1950703221 < 2147483647); omega) (by rfl)
#print axioms mul20
theorem add20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1008247216#u32 115515461#u32 604293221#u32 137235728#u32) c20=ok (q 275459953#u32 604525223#u32 474629208#u32 193853465#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1008247216 < 2147483647 ∧ 115515461 < 2147483647) ∧ (604293221 < 2147483647 ∧ 137235728 < 2147483647); omega) canonical20 (by rfl)
#print axioms add20
theorem mul19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 275459953#u32 604525223#u32 474629208#u32 193853465#u32) (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32)=ok (q 767993026#u32 346858738#u32 896469467#u32 30307998#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (275459953 < 2147483647 ∧ 604525223 < 2147483647) ∧ (474629208 < 2147483647 ∧ 193853465 < 2147483647); omega) (by change (1976533199 < 2147483647 ∧ 2142788478 < 2147483647) ∧ (1835806328 < 2147483647 ∧ 1950703221 < 2147483647); omega) (by rfl)
#print axioms mul19
theorem add19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 767993026#u32 346858738#u32 896469467#u32 30307998#u32) c19=ok (q 2063436947#u32 804810027#u32 1437813451#u32 2071705879#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (767993026 < 2147483647 ∧ 346858738 < 2147483647) ∧ (896469467 < 2147483647 ∧ 30307998 < 2147483647); omega) canonical19 (by rfl)
#print axioms add19
theorem mul18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2063436947#u32 804810027#u32 1437813451#u32 2071705879#u32) (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32)=ok (q 1544393611#u32 1979768093#u32 510673642#u32 1864655209#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2063436947 < 2147483647 ∧ 804810027 < 2147483647) ∧ (1437813451 < 2147483647 ∧ 2071705879 < 2147483647); omega) (by change (1976533199 < 2147483647 ∧ 2142788478 < 2147483647) ∧ (1835806328 < 2147483647 ∧ 1950703221 < 2147483647); omega) (by rfl)
#print axioms mul18
theorem add18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1544393611#u32 1979768093#u32 510673642#u32 1864655209#u32) c18=ok (q 316623072#u32 663498971#u32 1638238475#u32 328716165#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1544393611 < 2147483647 ∧ 1979768093 < 2147483647) ∧ (510673642 < 2147483647 ∧ 1864655209 < 2147483647); omega) canonical18 (by rfl)
#print axioms add18
theorem mul17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 316623072#u32 663498971#u32 1638238475#u32 328716165#u32) (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32)=ok (q 1837348519#u32 803703210#u32 653324216#u32 782385973#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (316623072 < 2147483647 ∧ 663498971 < 2147483647) ∧ (1638238475 < 2147483647 ∧ 328716165 < 2147483647); omega) (by change (1976533199 < 2147483647 ∧ 2142788478 < 2147483647) ∧ (1835806328 < 2147483647 ∧ 1950703221 < 2147483647); omega) (by rfl)
#print axioms mul17
theorem add17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1837348519#u32 803703210#u32 653324216#u32 782385973#u32) c17=ok (q 384712018#u32 1487646048#u32 279015340#u32 1075475789#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1837348519 < 2147483647 ∧ 803703210 < 2147483647) ∧ (653324216 < 2147483647 ∧ 782385973 < 2147483647); omega) canonical17 (by rfl)
#print axioms add17
theorem mul16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 384712018#u32 1487646048#u32 279015340#u32 1075475789#u32) (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32)=ok (q 886396516#u32 939841872#u32 974372567#u32 49270341#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (384712018 < 2147483647 ∧ 1487646048 < 2147483647) ∧ (279015340 < 2147483647 ∧ 1075475789 < 2147483647); omega) (by change (1976533199 < 2147483647 ∧ 2142788478 < 2147483647) ∧ (1835806328 < 2147483647 ∧ 1950703221 < 2147483647); omega) (by rfl)
#print axioms mul16
theorem add16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 886396516#u32 939841872#u32 974372567#u32 49270341#u32) c16=ok (q 115248260#u32 1011083439#u32 960335011#u32 1164626126#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (886396516 < 2147483647 ∧ 939841872 < 2147483647) ∧ (974372567 < 2147483647 ∧ 49270341 < 2147483647); omega) canonical16 (by rfl)
#print axioms add16
theorem mul15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 115248260#u32 1011083439#u32 960335011#u32 1164626126#u32) (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32)=ok (q 1837759740#u32 1800388171#u32 302801309#u32 1742835426#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (115248260 < 2147483647 ∧ 1011083439 < 2147483647) ∧ (960335011 < 2147483647 ∧ 1164626126 < 2147483647); omega) (by change (1976533199 < 2147483647 ∧ 2142788478 < 2147483647) ∧ (1835806328 < 2147483647 ∧ 1950703221 < 2147483647); omega) (by rfl)
#print axioms mul15
theorem add15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1837759740#u32 1800388171#u32 302801309#u32 1742835426#u32) c15=ok (q 902907557#u32 654025014#u32 1525660006#u32 1758902633#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1837759740 < 2147483647 ∧ 1800388171 < 2147483647) ∧ (302801309 < 2147483647 ∧ 1742835426 < 2147483647); omega) canonical15 (by rfl)
#print axioms add15
theorem mul14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 902907557#u32 654025014#u32 1525660006#u32 1758902633#u32) (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32)=ok (q 1164634071#u32 1710788929#u32 1531551056#u32 698559721#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (902907557 < 2147483647 ∧ 654025014 < 2147483647) ∧ (1525660006 < 2147483647 ∧ 1758902633 < 2147483647); omega) (by change (1976533199 < 2147483647 ∧ 2142788478 < 2147483647) ∧ (1835806328 < 2147483647 ∧ 1950703221 < 2147483647); omega) (by rfl)
#print axioms mul14
theorem add14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1164634071#u32 1710788929#u32 1531551056#u32 698559721#u32) c14=ok (q 1259000379#u32 1972168632#u32 520012117#u32 457902977#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1164634071 < 2147483647 ∧ 1710788929 < 2147483647) ∧ (1531551056 < 2147483647 ∧ 698559721 < 2147483647); omega) canonical14 (by rfl)
#print axioms add14
def final : Q := (q 1259000379#u32 1972168632#u32 520012117#u32 457902977#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 5#usize 28#usize initial 14#usize final := by
  refine .step (by change 28>0; omega) (JFr_IndexArithmetic.sub 28#usize 27#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32) from rfl) mul27 (show Array.index_usize p 27#usize=ok c27 from rfl) add27 ?_
  refine .step (by change 27>0; omega) (JFr_IndexArithmetic.sub 27#usize 26#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32) from rfl) mul26 (show Array.index_usize p 26#usize=ok c26 from rfl) add26 ?_
  refine .step (by change 26>0; omega) (JFr_IndexArithmetic.sub 26#usize 25#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32) from rfl) mul25 (show Array.index_usize p 25#usize=ok c25 from rfl) add25 ?_
  refine .step (by change 25>0; omega) (JFr_IndexArithmetic.sub 25#usize 24#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32) from rfl) mul24 (show Array.index_usize p 24#usize=ok c24 from rfl) add24 ?_
  refine .step (by change 24>0; omega) (JFr_IndexArithmetic.sub 24#usize 23#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32) from rfl) mul23 (show Array.index_usize p 23#usize=ok c23 from rfl) add23 ?_
  refine .step (by change 23>0; omega) (JFr_IndexArithmetic.sub 23#usize 22#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32) from rfl) mul22 (show Array.index_usize p 22#usize=ok c22 from rfl) add22 ?_
  refine .step (by change 22>0; omega) (JFr_IndexArithmetic.sub 22#usize 21#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32) from rfl) mul21 (show Array.index_usize p 21#usize=ok c21 from rfl) add21 ?_
  refine .step (by change 21>0; omega) (JFr_IndexArithmetic.sub 21#usize 20#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32) from rfl) mul20 (show Array.index_usize p 20#usize=ok c20 from rfl) add20 ?_
  refine .step (by change 20>0; omega) (JFr_IndexArithmetic.sub 20#usize 19#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32) from rfl) mul19 (show Array.index_usize p 19#usize=ok c19 from rfl) add19 ?_
  refine .step (by change 19>0; omega) (JFr_IndexArithmetic.sub 19#usize 18#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32) from rfl) mul18 (show Array.index_usize p 18#usize=ok c18 from rfl) add18 ?_
  refine .step (by change 18>0; omega) (JFr_IndexArithmetic.sub 18#usize 17#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32) from rfl) mul17 (show Array.index_usize p 17#usize=ok c17 from rfl) add17 ?_
  refine .step (by change 17>0; omega) (JFr_IndexArithmetic.sub 17#usize 16#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32) from rfl) mul16 (show Array.index_usize p 16#usize=ok c16 from rfl) add16 ?_
  refine .step (by change 16>0; omega) (JFr_IndexArithmetic.sub 16#usize 15#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32) from rfl) mul15 (show Array.index_usize p 15#usize=ok c15 from rfl) add15 ?_
  refine .step (by change 15>0; omega) (JFr_IndexArithmetic.sub 15#usize 14#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 1976533199#u32 2142788478#u32 1835806328#u32 1950703221#u32) from rfl) mul14 (show Array.index_usize p 14#usize=ok c14 from rfl) add14 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner05_0
