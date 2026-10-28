import NDO_JFr_Data05
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner05_0
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data05
def initial : Q := (q 0#u32 0#u32 0#u32 0#u32)
theorem mul27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 0#u32 0#u32 0#u32 0#u32) (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32)=ok (q 0#u32 0#u32 0#u32 0#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) (by change (810819047 < 2147483647 ∧ 1156380883 < 2147483647) ∧ (768810467 < 2147483647 ∧ 1018558903 < 2147483647); omega) (by rfl)
#print axioms mul27
theorem add27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 0#u32 0#u32 0#u32 0#u32) c27=ok (q 422822677#u32 1335527848#u32 1869469429#u32 740600032#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) canonical27 (by rfl)
#print axioms add27
theorem mul26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 422822677#u32 1335527848#u32 1869469429#u32 740600032#u32) (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32)=ok (q 1939503272#u32 17982192#u32 491090950#u32 606559641#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (422822677 < 2147483647 ∧ 1335527848 < 2147483647) ∧ (1869469429 < 2147483647 ∧ 740600032 < 2147483647); omega) (by change (810819047 < 2147483647 ∧ 1156380883 < 2147483647) ∧ (768810467 < 2147483647 ∧ 1018558903 < 2147483647); omega) (by rfl)
#print axioms mul26
theorem add26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1939503272#u32 17982192#u32 491090950#u32 606559641#u32) c26=ok (q 954141763#u32 1451205437#u32 1909382392#u32 1650777139#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1939503272 < 2147483647 ∧ 17982192 < 2147483647) ∧ (491090950 < 2147483647 ∧ 606559641 < 2147483647); omega) canonical26 (by rfl)
#print axioms add26
theorem mul25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 954141763#u32 1451205437#u32 1909382392#u32 1650777139#u32) (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32)=ok (q 2053697990#u32 311783484#u32 220991246#u32 1374778952#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (954141763 < 2147483647 ∧ 1451205437 < 2147483647) ∧ (1909382392 < 2147483647 ∧ 1650777139 < 2147483647); omega) (by change (810819047 < 2147483647 ∧ 1156380883 < 2147483647) ∧ (768810467 < 2147483647 ∧ 1018558903 < 2147483647); omega) (by rfl)
#print axioms mul25
theorem add25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2053697990#u32 311783484#u32 220991246#u32 1374778952#u32) c25=ok (q 1089143492#u32 1242631371#u32 1651536160#u32 703090728#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2053697990 < 2147483647 ∧ 311783484 < 2147483647) ∧ (220991246 < 2147483647 ∧ 1374778952 < 2147483647); omega) canonical25 (by rfl)
#print axioms add25
theorem mul24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1089143492#u32 1242631371#u32 1651536160#u32 703090728#u32) (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32)=ok (q 1943558535#u32 468519349#u32 1486042201#u32 2128760274#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1089143492 < 2147483647 ∧ 1242631371 < 2147483647) ∧ (1651536160 < 2147483647 ∧ 703090728 < 2147483647); omega) (by change (810819047 < 2147483647 ∧ 1156380883 < 2147483647) ∧ (768810467 < 2147483647 ∧ 1018558903 < 2147483647); omega) (by rfl)
#print axioms mul24
theorem add24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1943558535#u32 468519349#u32 1486042201#u32 2128760274#u32) c24=ok (q 1228149471#u32 91832689#u32 1441261941#u32 749712195#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1943558535 < 2147483647 ∧ 468519349 < 2147483647) ∧ (1486042201 < 2147483647 ∧ 2128760274 < 2147483647); omega) canonical24 (by rfl)
#print axioms add24
theorem mul23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1228149471#u32 91832689#u32 1441261941#u32 749712195#u32) (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32)=ok (q 1532362138#u32 322375761#u32 1354454482#u32 1042347913#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1228149471 < 2147483647 ∧ 91832689 < 2147483647) ∧ (1441261941 < 2147483647 ∧ 749712195 < 2147483647); omega) (by change (810819047 < 2147483647 ∧ 1156380883 < 2147483647) ∧ (768810467 < 2147483647 ∧ 1018558903 < 2147483647); omega) (by rfl)
#print axioms mul23
theorem add23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1532362138#u32 322375761#u32 1354454482#u32 1042347913#u32) c23=ok (q 1631843719#u32 1720789336#u32 2026382897#u32 1606209641#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1532362138 < 2147483647 ∧ 322375761 < 2147483647) ∧ (1354454482 < 2147483647 ∧ 1042347913 < 2147483647); omega) canonical23 (by rfl)
#print axioms add23
theorem mul22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1631843719#u32 1720789336#u32 2026382897#u32 1606209641#u32) (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32)=ok (q 1514928666#u32 773040087#u32 588166583#u32 174282989#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1631843719 < 2147483647 ∧ 1720789336 < 2147483647) ∧ (2026382897 < 2147483647 ∧ 1606209641 < 2147483647); omega) (by change (810819047 < 2147483647 ∧ 1156380883 < 2147483647) ∧ (768810467 < 2147483647 ∧ 1018558903 < 2147483647); omega) (by rfl)
#print axioms mul22
theorem add22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1514928666#u32 773040087#u32 588166583#u32 174282989#u32) c22=ok (q 1757432188#u32 611345026#u32 668345544#u32 1456605445#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1514928666 < 2147483647 ∧ 773040087 < 2147483647) ∧ (588166583 < 2147483647 ∧ 174282989 < 2147483647); omega) canonical22 (by rfl)
#print axioms add22
theorem mul21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1757432188#u32 611345026#u32 668345544#u32 1456605445#u32) (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32)=ok (q 653963654#u32 1244032256#u32 470349636#u32 1379400880#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1757432188 < 2147483647 ∧ 611345026 < 2147483647) ∧ (668345544 < 2147483647 ∧ 1456605445 < 2147483647); omega) (by change (810819047 < 2147483647 ∧ 1156380883 < 2147483647) ∧ (768810467 < 2147483647 ∧ 1018558903 < 2147483647); omega) (by rfl)
#print axioms mul21
theorem add21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 653963654#u32 1244032256#u32 470349636#u32 1379400880#u32) c21=ok (q 922102650#u32 1573466159#u32 1535206285#u32 1487873833#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (653963654 < 2147483647 ∧ 1244032256 < 2147483647) ∧ (470349636 < 2147483647 ∧ 1379400880 < 2147483647); omega) canonical21 (by rfl)
#print axioms add21
theorem mul20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 922102650#u32 1573466159#u32 1535206285#u32 1487873833#u32) (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32)=ok (q 135440982#u32 16028189#u32 17366622#u32 1887795446#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (922102650 < 2147483647 ∧ 1573466159 < 2147483647) ∧ (1535206285 < 2147483647 ∧ 1487873833 < 2147483647); omega) (by change (810819047 < 2147483647 ∧ 1156380883 < 2147483647) ∧ (768810467 < 2147483647 ∧ 1018558903 < 2147483647); omega) (by rfl)
#print axioms mul20
theorem add20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 135440982#u32 16028189#u32 17366622#u32 1887795446#u32) c20=ok (q 896290833#u32 614618134#u32 7268019#u32 882679080#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (135440982 < 2147483647 ∧ 16028189 < 2147483647) ∧ (17366622 < 2147483647 ∧ 1887795446 < 2147483647); omega) canonical20 (by rfl)
#print axioms add20
theorem mul19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 896290833#u32 614618134#u32 7268019#u32 882679080#u32) (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32)=ok (q 1788612207#u32 826539218#u32 1980751490#u32 883028937#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (896290833 < 2147483647 ∧ 614618134 < 2147483647) ∧ (7268019 < 2147483647 ∧ 882679080 < 2147483647); omega) (by change (810819047 < 2147483647 ∧ 1156380883 < 2147483647) ∧ (768810467 < 2147483647 ∧ 1018558903 < 2147483647); omega) (by rfl)
#print axioms mul19
theorem add19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1788612207#u32 826539218#u32 1980751490#u32 883028937#u32) c19=ok (q 1736913286#u32 1614946712#u32 2048706807#u32 1309998296#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1788612207 < 2147483647 ∧ 826539218 < 2147483647) ∧ (1980751490 < 2147483647 ∧ 883028937 < 2147483647); omega) canonical19 (by rfl)
#print axioms add19
theorem mul18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1736913286#u32 1614946712#u32 2048706807#u32 1309998296#u32) (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32)=ok (q 966625192#u32 1928750724#u32 40349024#u32 346449604#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1736913286 < 2147483647 ∧ 1614946712 < 2147483647) ∧ (2048706807 < 2147483647 ∧ 1309998296 < 2147483647); omega) (by change (810819047 < 2147483647 ∧ 1156380883 < 2147483647) ∧ (768810467 < 2147483647 ∧ 1018558903 < 2147483647); omega) (by rfl)
#print axioms mul18
theorem add18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 966625192#u32 1928750724#u32 40349024#u32 346449604#u32) c18=ok (q 2122319087#u32 176779547#u32 1342940656#u32 1319423817#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (966625192 < 2147483647 ∧ 1928750724 < 2147483647) ∧ (40349024 < 2147483647 ∧ 346449604 < 2147483647); omega) canonical18 (by rfl)
#print axioms add18
theorem mul17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2122319087#u32 176779547#u32 1342940656#u32 1319423817#u32) (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32)=ok (q 302325926#u32 1347398772#u32 1644019737#u32 797791971#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2122319087 < 2147483647 ∧ 176779547 < 2147483647) ∧ (1342940656 < 2147483647 ∧ 1319423817 < 2147483647); omega) (by change (810819047 < 2147483647 ∧ 1156380883 < 2147483647) ∧ (768810467 < 2147483647 ∧ 1018558903 < 2147483647); omega) (by rfl)
#print axioms mul17
theorem add17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 302325926#u32 1347398772#u32 1644019737#u32 797791971#u32) c17=ok (q 778036591#u32 590543590#u32 908063314#u32 186572799#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (302325926 < 2147483647 ∧ 1347398772 < 2147483647) ∧ (1644019737 < 2147483647 ∧ 797791971 < 2147483647); omega) canonical17 (by rfl)
#print axioms add17
theorem mul16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 778036591#u32 590543590#u32 908063314#u32 186572799#u32) (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32)=ok (q 667158652#u32 1731302362#u32 627970295#u32 887658693#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (778036591 < 2147483647 ∧ 590543590 < 2147483647) ∧ (908063314 < 2147483647 ∧ 186572799 < 2147483647); omega) (by change (810819047 < 2147483647 ∧ 1156380883 < 2147483647) ∧ (768810467 < 2147483647 ∧ 1018558903 < 2147483647); omega) (by rfl)
#print axioms mul16
theorem add16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 667158652#u32 1731302362#u32 627970295#u32 887658693#u32) c16=ok (q 6697070#u32 1896924594#u32 697555010#u32 43870661#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (667158652 < 2147483647 ∧ 1731302362 < 2147483647) ∧ (627970295 < 2147483647 ∧ 887658693 < 2147483647); omega) canonical16 (by rfl)
#print axioms add16
theorem mul15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 6697070#u32 1896924594#u32 697555010#u32 43870661#u32) (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32)=ok (q 2050772013#u32 2011734018#u32 53400170#u32 282075402#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (6697070 < 2147483647 ∧ 1896924594 < 2147483647) ∧ (697555010 < 2147483647 ∧ 43870661 < 2147483647); omega) (by change (810819047 < 2147483647 ∧ 1156380883 < 2147483647) ∧ (768810467 < 2147483647 ∧ 1018558903 < 2147483647); omega) (by rfl)
#print axioms mul15
theorem add15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2050772013#u32 2011734018#u32 53400170#u32 282075402#u32) c15=ok (q 1185758199#u32 1450833123#u32 540837724#u32 965434775#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2050772013 < 2147483647 ∧ 2011734018 < 2147483647) ∧ (53400170 < 2147483647 ∧ 282075402 < 2147483647); omega) canonical15 (by rfl)
#print axioms add15
theorem mul14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1185758199#u32 1450833123#u32 540837724#u32 965434775#u32) (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32)=ok (q 1075143522#u32 20559562#u32 2147360506#u32 487871075#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1185758199 < 2147483647 ∧ 1450833123 < 2147483647) ∧ (540837724 < 2147483647 ∧ 965434775 < 2147483647); omega) (by change (810819047 < 2147483647 ∧ 1156380883 < 2147483647) ∧ (768810467 < 2147483647 ∧ 1018558903 < 2147483647); omega) (by rfl)
#print axioms mul14
theorem add14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1075143522#u32 20559562#u32 2147360506#u32 487871075#u32) c14=ok (q 2094586920#u32 1154417908#u32 1213740484#u32 1672019413#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1075143522 < 2147483647 ∧ 20559562 < 2147483647) ∧ (2147360506 < 2147483647 ∧ 487871075 < 2147483647); omega) canonical14 (by rfl)
#print axioms add14
def final : Q := (q 2094586920#u32 1154417908#u32 1213740484#u32 1672019413#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 5#usize 28#usize initial 14#usize final := by
  refine .step (by change 28>0; omega) (JFr_IndexArithmetic.sub 28#usize 27#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32) from rfl) mul27 (show Array.index_usize p 27#usize=ok c27 from rfl) add27 ?_
  refine .step (by change 27>0; omega) (JFr_IndexArithmetic.sub 27#usize 26#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32) from rfl) mul26 (show Array.index_usize p 26#usize=ok c26 from rfl) add26 ?_
  refine .step (by change 26>0; omega) (JFr_IndexArithmetic.sub 26#usize 25#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32) from rfl) mul25 (show Array.index_usize p 25#usize=ok c25 from rfl) add25 ?_
  refine .step (by change 25>0; omega) (JFr_IndexArithmetic.sub 25#usize 24#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32) from rfl) mul24 (show Array.index_usize p 24#usize=ok c24 from rfl) add24 ?_
  refine .step (by change 24>0; omega) (JFr_IndexArithmetic.sub 24#usize 23#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32) from rfl) mul23 (show Array.index_usize p 23#usize=ok c23 from rfl) add23 ?_
  refine .step (by change 23>0; omega) (JFr_IndexArithmetic.sub 23#usize 22#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32) from rfl) mul22 (show Array.index_usize p 22#usize=ok c22 from rfl) add22 ?_
  refine .step (by change 22>0; omega) (JFr_IndexArithmetic.sub 22#usize 21#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32) from rfl) mul21 (show Array.index_usize p 21#usize=ok c21 from rfl) add21 ?_
  refine .step (by change 21>0; omega) (JFr_IndexArithmetic.sub 21#usize 20#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32) from rfl) mul20 (show Array.index_usize p 20#usize=ok c20 from rfl) add20 ?_
  refine .step (by change 20>0; omega) (JFr_IndexArithmetic.sub 20#usize 19#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32) from rfl) mul19 (show Array.index_usize p 19#usize=ok c19 from rfl) add19 ?_
  refine .step (by change 19>0; omega) (JFr_IndexArithmetic.sub 19#usize 18#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32) from rfl) mul18 (show Array.index_usize p 18#usize=ok c18 from rfl) add18 ?_
  refine .step (by change 18>0; omega) (JFr_IndexArithmetic.sub 18#usize 17#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32) from rfl) mul17 (show Array.index_usize p 17#usize=ok c17 from rfl) add17 ?_
  refine .step (by change 17>0; omega) (JFr_IndexArithmetic.sub 17#usize 16#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32) from rfl) mul16 (show Array.index_usize p 16#usize=ok c16 from rfl) add16 ?_
  refine .step (by change 16>0; omega) (JFr_IndexArithmetic.sub 16#usize 15#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32) from rfl) mul15 (show Array.index_usize p 15#usize=ok c15 from rfl) add15 ?_
  refine .step (by change 15>0; omega) (JFr_IndexArithmetic.sub 15#usize 14#usize rfl) (show Array.index_usize alpha 5#usize=ok (q 810819047#u32 1156380883#u32 768810467#u32 1018558903#u32) from rfl) mul14 (show Array.index_usize p 14#usize=ok c14 from rfl) add14 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner05_0
