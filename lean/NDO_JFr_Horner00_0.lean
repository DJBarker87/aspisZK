import NDO_JFr_Data00
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner00_0
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data00
def initial : Q := (q 0#u32 0#u32 0#u32 0#u32)
theorem mul27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 0#u32 0#u32 0#u32 0#u32) (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32)=ok (q 0#u32 0#u32 0#u32 0#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) (by change (705343446 < 2147483647 ∧ 1948609717 < 2147483647) ∧ (871005084 < 2147483647 ∧ 203308705 < 2147483647); omega) (by rfl)
#print axioms mul27
theorem add27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 0#u32 0#u32 0#u32 0#u32) c27=ok (q 1758090677#u32 1269898450#u32 604044076#u32 2081632309#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) canonical27 (by rfl)
#print axioms add27
theorem mul26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1758090677#u32 1269898450#u32 604044076#u32 2081632309#u32) (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32)=ok (q 653686126#u32 1223970888#u32 2117242845#u32 1309796238#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1758090677 < 2147483647 ∧ 1269898450 < 2147483647) ∧ (604044076 < 2147483647 ∧ 2081632309 < 2147483647); omega) (by change (705343446 < 2147483647 ∧ 1948609717 < 2147483647) ∧ (871005084 < 2147483647 ∧ 203308705 < 2147483647); omega) (by rfl)
#print axioms mul26
theorem add26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 653686126#u32 1223970888#u32 2117242845#u32 1309796238#u32) c26=ok (q 1473678914#u32 147932901#u32 89443327#u32 880654170#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (653686126 < 2147483647 ∧ 1223970888 < 2147483647) ∧ (2117242845 < 2147483647 ∧ 1309796238 < 2147483647); omega) canonical26 (by rfl)
#print axioms add26
theorem mul25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1473678914#u32 147932901#u32 89443327#u32 880654170#u32) (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32)=ok (q 1905491338#u32 1105841931#u32 1187268419#u32 1154595464#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1473678914 < 2147483647 ∧ 147932901 < 2147483647) ∧ (89443327 < 2147483647 ∧ 880654170 < 2147483647); omega) (by change (705343446 < 2147483647 ∧ 1948609717 < 2147483647) ∧ (871005084 < 2147483647 ∧ 203308705 < 2147483647); omega) (by rfl)
#print axioms mul25
theorem add25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1905491338#u32 1105841931#u32 1187268419#u32 1154595464#u32) c25=ok (q 1355730385#u32 656819388#u32 1409837134#u32 1552592581#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1905491338 < 2147483647 ∧ 1105841931 < 2147483647) ∧ (1187268419 < 2147483647 ∧ 1154595464 < 2147483647); omega) canonical25 (by rfl)
#print axioms add25
theorem mul24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1355730385#u32 656819388#u32 1409837134#u32 1552592581#u32) (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32)=ok (q 1077876347#u32 997294266#u32 1761970900#u32 185896428#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1355730385 < 2147483647 ∧ 656819388 < 2147483647) ∧ (1409837134 < 2147483647 ∧ 1552592581 < 2147483647); omega) (by change (705343446 < 2147483647 ∧ 1948609717 < 2147483647) ∧ (871005084 < 2147483647 ∧ 203308705 < 2147483647); omega) (by rfl)
#print axioms mul24
theorem add24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1077876347#u32 997294266#u32 1761970900#u32 185896428#u32) c24=ok (q 516167553#u32 1393080727#u32 124845718#u32 1235930154#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1077876347 < 2147483647 ∧ 997294266 < 2147483647) ∧ (1761970900 < 2147483647 ∧ 185896428 < 2147483647); omega) canonical24 (by rfl)
#print axioms add24
theorem mul23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 516167553#u32 1393080727#u32 124845718#u32 1235930154#u32) (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32)=ok (q 472186476#u32 837061492#u32 388807283#u32 1361270487#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (516167553 < 2147483647 ∧ 1393080727 < 2147483647) ∧ (124845718 < 2147483647 ∧ 1235930154 < 2147483647); omega) (by change (705343446 < 2147483647 ∧ 1948609717 < 2147483647) ∧ (871005084 < 2147483647 ∧ 203308705 < 2147483647); omega) (by rfl)
#print axioms mul23
theorem add23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 472186476#u32 837061492#u32 388807283#u32 1361270487#u32) c23=ok (q 1055685492#u32 1251803419#u32 1170367058#u32 586202862#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (472186476 < 2147483647 ∧ 837061492 < 2147483647) ∧ (388807283 < 2147483647 ∧ 1361270487 < 2147483647); omega) canonical23 (by rfl)
#print axioms add23
theorem mul22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1055685492#u32 1251803419#u32 1170367058#u32 586202862#u32) (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32)=ok (q 200478885#u32 598417674#u32 1689317075#u32 1961724322#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1055685492 < 2147483647 ∧ 1251803419 < 2147483647) ∧ (1170367058 < 2147483647 ∧ 586202862 < 2147483647); omega) (by change (705343446 < 2147483647 ∧ 1948609717 < 2147483647) ∧ (871005084 < 2147483647 ∧ 203308705 < 2147483647); omega) (by rfl)
#print axioms mul22
theorem add22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 200478885#u32 598417674#u32 1689317075#u32 1961724322#u32) c22=ok (q 1518249393#u32 188485020#u32 1377194060#u32 981013102#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (200478885 < 2147483647 ∧ 598417674 < 2147483647) ∧ (1689317075 < 2147483647 ∧ 1961724322 < 2147483647); omega) canonical22 (by rfl)
#print axioms add22
theorem mul21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1518249393#u32 188485020#u32 1377194060#u32 981013102#u32) (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32)=ok (q 613893392#u32 1366405384#u32 1208131351#u32 1456298338#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1518249393 < 2147483647 ∧ 188485020 < 2147483647) ∧ (1377194060 < 2147483647 ∧ 981013102 < 2147483647); omega) (by change (705343446 < 2147483647 ∧ 1948609717 < 2147483647) ∧ (871005084 < 2147483647 ∧ 203308705 < 2147483647); omega) (by rfl)
#print axioms mul21
theorem add21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 613893392#u32 1366405384#u32 1208131351#u32 1456298338#u32) c21=ok (q 1021757676#u32 954181566#u32 905675181#u32 516859948#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (613893392 < 2147483647 ∧ 1366405384 < 2147483647) ∧ (1208131351 < 2147483647 ∧ 1456298338 < 2147483647); omega) canonical21 (by rfl)
#print axioms add21
theorem mul20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1021757676#u32 954181566#u32 905675181#u32 516859948#u32) (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32)=ok (q 650391048#u32 128932166#u32 2141806252#u32 669697374#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1021757676 < 2147483647 ∧ 954181566 < 2147483647) ∧ (905675181 < 2147483647 ∧ 516859948 < 2147483647); omega) (by change (705343446 < 2147483647 ∧ 1948609717 < 2147483647) ∧ (871005084 < 2147483647 ∧ 203308705 < 2147483647); omega) (by rfl)
#print axioms mul20
theorem add20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 650391048#u32 128932166#u32 2141806252#u32 669697374#u32) c20=ok (q 575619142#u32 507021701#u32 1625254919#u32 1353208454#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (650391048 < 2147483647 ∧ 128932166 < 2147483647) ∧ (2141806252 < 2147483647 ∧ 669697374 < 2147483647); omega) canonical20 (by rfl)
#print axioms add20
theorem mul19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 575619142#u32 507021701#u32 1625254919#u32 1353208454#u32) (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32)=ok (q 2090142098#u32 1434726213#u32 1746375384#u32 428027787#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (575619142 < 2147483647 ∧ 507021701 < 2147483647) ∧ (1625254919 < 2147483647 ∧ 1353208454 < 2147483647); omega) (by change (705343446 < 2147483647 ∧ 1948609717 < 2147483647) ∧ (871005084 < 2147483647 ∧ 203308705 < 2147483647); omega) (by rfl)
#print axioms mul19
theorem add19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2090142098#u32 1434726213#u32 1746375384#u32 428027787#u32) c19=ok (q 284582904#u32 1344315862#u32 1440364980#u32 2089928230#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2090142098 < 2147483647 ∧ 1434726213 < 2147483647) ∧ (1746375384 < 2147483647 ∧ 428027787 < 2147483647); omega) canonical19 (by rfl)
#print axioms add19
theorem mul18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 284582904#u32 1344315862#u32 1440364980#u32 2089928230#u32) (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32)=ok (q 740467821#u32 785403251#u32 759569964#u32 1155119145#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (284582904 < 2147483647 ∧ 1344315862 < 2147483647) ∧ (1440364980 < 2147483647 ∧ 2089928230 < 2147483647); omega) (by change (705343446 < 2147483647 ∧ 1948609717 < 2147483647) ∧ (871005084 < 2147483647 ∧ 203308705 < 2147483647); omega) (by rfl)
#print axioms mul18
theorem add18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 740467821#u32 785403251#u32 759569964#u32 1155119145#u32) c18=ok (q 1213096832#u32 401298686#u32 1630523243#u32 1229820529#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (740467821 < 2147483647 ∧ 785403251 < 2147483647) ∧ (759569964 < 2147483647 ∧ 1155119145 < 2147483647); omega) canonical18 (by rfl)
#print axioms add18
theorem mul17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1213096832#u32 401298686#u32 1630523243#u32 1229820529#u32) (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32)=ok (q 605753182#u32 303321362#u32 1722517674#u32 2009215435#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1213096832 < 2147483647 ∧ 401298686 < 2147483647) ∧ (1630523243 < 2147483647 ∧ 1229820529 < 2147483647); omega) (by change (705343446 < 2147483647 ∧ 1948609717 < 2147483647) ∧ (871005084 < 2147483647 ∧ 203308705 < 2147483647); omega) (by rfl)
#print axioms mul17
theorem add17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 605753182#u32 303321362#u32 1722517674#u32 2009215435#u32) c17=ok (q 69138812#u32 465668689#u32 1565926452#u32 910142217#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (605753182 < 2147483647 ∧ 303321362 < 2147483647) ∧ (1722517674 < 2147483647 ∧ 2009215435 < 2147483647); omega) canonical17 (by rfl)
#print axioms add17
theorem mul16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 69138812#u32 465668689#u32 1565926452#u32 910142217#u32) (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32)=ok (q 817312569#u32 422916318#u32 304858669#u32 926312864#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (69138812 < 2147483647 ∧ 465668689 < 2147483647) ∧ (1565926452 < 2147483647 ∧ 910142217 < 2147483647); omega) (by change (705343446 < 2147483647 ∧ 1948609717 < 2147483647) ∧ (871005084 < 2147483647 ∧ 203308705 < 2147483647); omega) (by rfl)
#print axioms mul16
theorem add16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 817312569#u32 422916318#u32 304858669#u32 926312864#u32) c16=ok (q 1465521920#u32 1324658153#u32 1536059533#u32 301280692#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (817312569 < 2147483647 ∧ 422916318 < 2147483647) ∧ (304858669 < 2147483647 ∧ 926312864 < 2147483647); omega) canonical16 (by rfl)
#print axioms add16
theorem mul15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1465521920#u32 1324658153#u32 1536059533#u32 301280692#u32) (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32)=ok (q 1237051018#u32 312013134#u32 1237384873#u32 1099499902#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1465521920 < 2147483647 ∧ 1324658153 < 2147483647) ∧ (1536059533 < 2147483647 ∧ 301280692 < 2147483647); omega) (by change (705343446 < 2147483647 ∧ 1948609717 < 2147483647) ∧ (871005084 < 2147483647 ∧ 203308705 < 2147483647); omega) (by rfl)
#print axioms mul15
theorem add15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1237051018#u32 312013134#u32 1237384873#u32 1099499902#u32) c15=ok (q 2089730883#u32 403842398#u32 721084491#u32 1608350248#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1237051018 < 2147483647 ∧ 312013134 < 2147483647) ∧ (1237384873 < 2147483647 ∧ 1099499902 < 2147483647); omega) canonical15 (by rfl)
#print axioms add15
theorem mul14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2089730883#u32 403842398#u32 721084491#u32 1608350248#u32) (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32)=ok (q 977420636#u32 1231741840#u32 1745044674#u32 267608644#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2089730883 < 2147483647 ∧ 403842398 < 2147483647) ∧ (721084491 < 2147483647 ∧ 1608350248 < 2147483647); omega) (by change (705343446 < 2147483647 ∧ 1948609717 < 2147483647) ∧ (871005084 < 2147483647 ∧ 203308705 < 2147483647); omega) (by rfl)
#print axioms mul14
theorem add14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 977420636#u32 1231741840#u32 1745044674#u32 267608644#u32) c14=ok (q 812910159#u32 714244792#u32 348845800#u32 1897507794#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (977420636 < 2147483647 ∧ 1231741840 < 2147483647) ∧ (1745044674 < 2147483647 ∧ 267608644 < 2147483647); omega) canonical14 (by rfl)
#print axioms add14
def final : Q := (q 812910159#u32 714244792#u32 348845800#u32 1897507794#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 0#usize 28#usize initial 14#usize final := by
  refine .step (by change 28>0; omega) (JFr_IndexArithmetic.sub 28#usize 27#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32) from rfl) mul27 (show Array.index_usize p 27#usize=ok c27 from rfl) add27 ?_
  refine .step (by change 27>0; omega) (JFr_IndexArithmetic.sub 27#usize 26#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32) from rfl) mul26 (show Array.index_usize p 26#usize=ok c26 from rfl) add26 ?_
  refine .step (by change 26>0; omega) (JFr_IndexArithmetic.sub 26#usize 25#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32) from rfl) mul25 (show Array.index_usize p 25#usize=ok c25 from rfl) add25 ?_
  refine .step (by change 25>0; omega) (JFr_IndexArithmetic.sub 25#usize 24#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32) from rfl) mul24 (show Array.index_usize p 24#usize=ok c24 from rfl) add24 ?_
  refine .step (by change 24>0; omega) (JFr_IndexArithmetic.sub 24#usize 23#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32) from rfl) mul23 (show Array.index_usize p 23#usize=ok c23 from rfl) add23 ?_
  refine .step (by change 23>0; omega) (JFr_IndexArithmetic.sub 23#usize 22#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32) from rfl) mul22 (show Array.index_usize p 22#usize=ok c22 from rfl) add22 ?_
  refine .step (by change 22>0; omega) (JFr_IndexArithmetic.sub 22#usize 21#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32) from rfl) mul21 (show Array.index_usize p 21#usize=ok c21 from rfl) add21 ?_
  refine .step (by change 21>0; omega) (JFr_IndexArithmetic.sub 21#usize 20#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32) from rfl) mul20 (show Array.index_usize p 20#usize=ok c20 from rfl) add20 ?_
  refine .step (by change 20>0; omega) (JFr_IndexArithmetic.sub 20#usize 19#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32) from rfl) mul19 (show Array.index_usize p 19#usize=ok c19 from rfl) add19 ?_
  refine .step (by change 19>0; omega) (JFr_IndexArithmetic.sub 19#usize 18#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32) from rfl) mul18 (show Array.index_usize p 18#usize=ok c18 from rfl) add18 ?_
  refine .step (by change 18>0; omega) (JFr_IndexArithmetic.sub 18#usize 17#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32) from rfl) mul17 (show Array.index_usize p 17#usize=ok c17 from rfl) add17 ?_
  refine .step (by change 17>0; omega) (JFr_IndexArithmetic.sub 17#usize 16#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32) from rfl) mul16 (show Array.index_usize p 16#usize=ok c16 from rfl) add16 ?_
  refine .step (by change 16>0; omega) (JFr_IndexArithmetic.sub 16#usize 15#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32) from rfl) mul15 (show Array.index_usize p 15#usize=ok c15 from rfl) add15 ?_
  refine .step (by change 15>0; omega) (JFr_IndexArithmetic.sub 15#usize 14#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 705343446#u32 1948609717#u32 871005084#u32 203308705#u32) from rfl) mul14 (show Array.index_usize p 14#usize=ok c14 from rfl) add14 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner00_0
