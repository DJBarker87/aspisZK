import NDO_JFr_Data01
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner01_0
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data01
def initial : Q := (q 0#u32 0#u32 0#u32 0#u32)
theorem mul27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 0#u32 0#u32 0#u32 0#u32) (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32)=ok (q 0#u32 0#u32 0#u32 0#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) (by change (1938229017 < 2147483647 ∧ 474903281 < 2147483647) ∧ (2119643323 < 2147483647 ∧ 1456121415 < 2147483647); omega) (by rfl)
#print axioms mul27
theorem add27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 0#u32 0#u32 0#u32 0#u32) c27=ok (q 562471256#u32 1416890178#u32 1783987022#u32 320981083#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) canonical27 (by rfl)
#print axioms add27
theorem mul26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 562471256#u32 1416890178#u32 1783987022#u32 320981083#u32) (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32)=ok (q 42485895#u32 1829775140#u32 1345659793#u32 163252419#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (562471256 < 2147483647 ∧ 1416890178 < 2147483647) ∧ (1783987022 < 2147483647 ∧ 320981083 < 2147483647); omega) (by change (1938229017 < 2147483647 ∧ 474903281 < 2147483647) ∧ (2119643323 < 2147483647 ∧ 1456121415 < 2147483647); omega) (by rfl)
#print axioms mul26
theorem add26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 42485895#u32 1829775140#u32 1345659793#u32 163252419#u32) c26=ok (q 2077554021#u32 1908588663#u32 1669982944#u32 561672465#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (42485895 < 2147483647 ∧ 1829775140 < 2147483647) ∧ (1345659793 < 2147483647 ∧ 163252419 < 2147483647); omega) canonical26 (by rfl)
#print axioms add26
theorem mul25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2077554021#u32 1908588663#u32 1669982944#u32 561672465#u32) (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32)=ok (q 2119787880#u32 1625849652#u32 1877825088#u32 534226640#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2077554021 < 2147483647 ∧ 1908588663 < 2147483647) ∧ (1669982944 < 2147483647 ∧ 561672465 < 2147483647); omega) (by change (1938229017 < 2147483647 ∧ 474903281 < 2147483647) ∧ (2119643323 < 2147483647 ∧ 1456121415 < 2147483647); omega) (by rfl)
#print axioms mul25
theorem add25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2119787880#u32 1625849652#u32 1877825088#u32 534226640#u32) c25=ok (q 1079997598#u32 746222991#u32 858860800#u32 1118896437#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2119787880 < 2147483647 ∧ 1625849652 < 2147483647) ∧ (1877825088 < 2147483647 ∧ 534226640 < 2147483647); omega) canonical25 (by rfl)
#print axioms add25
theorem mul24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1079997598#u32 746222991#u32 858860800#u32 1118896437#u32) (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32)=ok (q 452054032#u32 984013581#u32 1422841892#u32 1518719285#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1079997598 < 2147483647 ∧ 746222991 < 2147483647) ∧ (858860800 < 2147483647 ∧ 1118896437 < 2147483647); omega) (by change (1938229017 < 2147483647 ∧ 474903281 < 2147483647) ∧ (2119643323 < 2147483647 ∧ 1456121415 < 2147483647); omega) (by rfl)
#print axioms mul24
theorem add24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 452054032#u32 984013581#u32 1422841892#u32 1518719285#u32) c24=ok (q 114672033#u32 245187465#u32 911069968#u32 234015123#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (452054032 < 2147483647 ∧ 984013581 < 2147483647) ∧ (1422841892 < 2147483647 ∧ 1518719285 < 2147483647); omega) canonical24 (by rfl)
#print axioms add24
theorem mul23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 114672033#u32 245187465#u32 911069968#u32 234015123#u32) (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32)=ok (q 2119226668#u32 1629898004#u32 521975011#u32 1115750063#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (114672033 < 2147483647 ∧ 245187465 < 2147483647) ∧ (911069968 < 2147483647 ∧ 234015123 < 2147483647); omega) (by change (1938229017 < 2147483647 ∧ 474903281 < 2147483647) ∧ (2119643323 < 2147483647 ∧ 1456121415 < 2147483647); omega) (by rfl)
#print axioms mul23
theorem add23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2119226668#u32 1629898004#u32 521975011#u32 1115750063#u32) c23=ok (q 1412927636#u32 1807744191#u32 1661594377#u32 1024421429#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2119226668 < 2147483647 ∧ 1629898004 < 2147483647) ∧ (521975011 < 2147483647 ∧ 1115750063 < 2147483647); omega) canonical23 (by rfl)
#print axioms add23
theorem mul22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1412927636#u32 1807744191#u32 1661594377#u32 1024421429#u32) (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32)=ok (q 2060612622#u32 1819664873#u32 2054968391#u32 1261055443#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1412927636 < 2147483647 ∧ 1807744191 < 2147483647) ∧ (1661594377 < 2147483647 ∧ 1024421429 < 2147483647); omega) (by change (1938229017 < 2147483647 ∧ 474903281 < 2147483647) ∧ (2119643323 < 2147483647 ∧ 1456121415 < 2147483647); omega) (by rfl)
#print axioms mul22
theorem add22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2060612622#u32 1819664873#u32 2054968391#u32 1261055443#u32) c22=ok (q 352831125#u32 116088672#u32 1313032592#u32 1683783493#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2060612622 < 2147483647 ∧ 1819664873 < 2147483647) ∧ (2054968391 < 2147483647 ∧ 1261055443 < 2147483647); omega) canonical22 (by rfl)
#print axioms add22
theorem mul21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 352831125#u32 116088672#u32 1313032592#u32 1683783493#u32) (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32)=ok (q 1892913598#u32 1521760288#u32 1340999589#u32 952804378#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (352831125 < 2147483647 ∧ 116088672 < 2147483647) ∧ (1313032592 < 2147483647 ∧ 1683783493 < 2147483647); omega) (by change (1938229017 < 2147483647 ∧ 474903281 < 2147483647) ∧ (2119643323 < 2147483647 ∧ 1456121415 < 2147483647); omega) (by rfl)
#print axioms mul21
theorem add21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1892913598#u32 1521760288#u32 1340999589#u32 952804378#u32) c21=ok (q 1498640087#u32 1440447676#u32 358819770#u32 372464771#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1892913598 < 2147483647 ∧ 1521760288 < 2147483647) ∧ (1340999589 < 2147483647 ∧ 952804378 < 2147483647); omega) canonical21 (by rfl)
#print axioms add21
theorem mul20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1498640087#u32 1440447676#u32 358819770#u32 372464771#u32) (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32)=ok (q 1359072769#u32 1188419284#u32 1533981399#u32 1974386309#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1498640087 < 2147483647 ∧ 1440447676 < 2147483647) ∧ (358819770 < 2147483647 ∧ 372464771 < 2147483647); omega) (by change (1938229017 < 2147483647 ∧ 474903281 < 2147483647) ∧ (2119643323 < 2147483647 ∧ 1456121415 < 2147483647); omega) (by rfl)
#print axioms mul20
theorem add20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1359072769#u32 1188419284#u32 1533981399#u32 1974386309#u32) c20=ok (q 1191850009#u32 630152273#u32 1769800041#u32 192502710#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1359072769 < 2147483647 ∧ 1188419284 < 2147483647) ∧ (1533981399 < 2147483647 ∧ 1974386309 < 2147483647); omega) canonical20 (by rfl)
#print axioms add20
theorem mul19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1191850009#u32 630152273#u32 1769800041#u32 192502710#u32) (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32)=ok (q 994914493#u32 491719373#u32 2127689373#u32 551311425#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1191850009 < 2147483647 ∧ 630152273 < 2147483647) ∧ (1769800041 < 2147483647 ∧ 192502710 < 2147483647); omega) (by change (1938229017 < 2147483647 ∧ 474903281 < 2147483647) ∧ (2119643323 < 2147483647 ∧ 1456121415 < 2147483647); omega) (by rfl)
#print axioms mul19
theorem add19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 994914493#u32 491719373#u32 2127689373#u32 551311425#u32) c19=ok (q 1917836207#u32 1767364625#u32 730163569#u32 971833920#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (994914493 < 2147483647 ∧ 491719373 < 2147483647) ∧ (2127689373 < 2147483647 ∧ 551311425 < 2147483647); omega) canonical19 (by rfl)
#print axioms add19
theorem mul18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1917836207#u32 1767364625#u32 730163569#u32 971833920#u32) (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32)=ok (q 143954778#u32 1825237805#u32 668808506#u32 980991196#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1917836207 < 2147483647 ∧ 1767364625 < 2147483647) ∧ (730163569 < 2147483647 ∧ 971833920 < 2147483647); omega) (by change (1938229017 < 2147483647 ∧ 474903281 < 2147483647) ∧ (2119643323 < 2147483647 ∧ 1456121415 < 2147483647); omega) (by rfl)
#print axioms mul18
theorem add18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 143954778#u32 1825237805#u32 668808506#u32 980991196#u32) c18=ok (q 159344025#u32 172380770#u32 2101742522#u32 897295658#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (143954778 < 2147483647 ∧ 1825237805 < 2147483647) ∧ (668808506 < 2147483647 ∧ 980991196 < 2147483647); omega) canonical18 (by rfl)
#print axioms add18
theorem mul17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 159344025#u32 172380770#u32 2101742522#u32 897295658#u32) (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32)=ok (q 372877140#u32 1536359950#u32 1056975515#u32 875596846#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (159344025 < 2147483647 ∧ 172380770 < 2147483647) ∧ (2101742522 < 2147483647 ∧ 897295658 < 2147483647); omega) (by change (1938229017 < 2147483647 ∧ 474903281 < 2147483647) ∧ (2119643323 < 2147483647 ∧ 1456121415 < 2147483647); omega) (by rfl)
#print axioms mul17
theorem add17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 372877140#u32 1536359950#u32 1056975515#u32 875596846#u32) c17=ok (q 1046215939#u32 680072389#u32 981534392#u32 1020704599#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (372877140 < 2147483647 ∧ 1536359950 < 2147483647) ∧ (1056975515 < 2147483647 ∧ 875596846 < 2147483647); omega) canonical17 (by rfl)
#print axioms add17
theorem mul16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1046215939#u32 680072389#u32 981534392#u32 1020704599#u32) (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32)=ok (q 1905028724#u32 964996694#u32 95050697#u32 1265698266#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1046215939 < 2147483647 ∧ 680072389 < 2147483647) ∧ (981534392 < 2147483647 ∧ 1020704599 < 2147483647); omega) (by change (1938229017 < 2147483647 ∧ 474903281 < 2147483647) ∧ (2119643323 < 2147483647 ∧ 1456121415 < 2147483647); omega) (by rfl)
#print axioms mul16
theorem add16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1905028724#u32 964996694#u32 95050697#u32 1265698266#u32) c16=ok (q 1381856840#u32 872890578#u32 943060762#u32 491887429#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1905028724 < 2147483647 ∧ 964996694 < 2147483647) ∧ (95050697 < 2147483647 ∧ 1265698266 < 2147483647); omega) canonical16 (by rfl)
#print axioms add16
theorem mul15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1381856840#u32 872890578#u32 943060762#u32 491887429#u32) (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32)=ok (q 1382516761#u32 2051810923#u32 19891375#u32 1471528627#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1381856840 < 2147483647 ∧ 872890578 < 2147483647) ∧ (943060762 < 2147483647 ∧ 491887429 < 2147483647); omega) (by change (1938229017 < 2147483647 ∧ 474903281 < 2147483647) ∧ (2119643323 < 2147483647 ∧ 1456121415 < 2147483647); omega) (by rfl)
#print axioms mul15
theorem add15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1382516761#u32 2051810923#u32 19891375#u32 1471528627#u32) c15=ok (q 824678393#u32 1340474354#u32 1436153629#u32 2013791478#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1382516761 < 2147483647 ∧ 2051810923 < 2147483647) ∧ (19891375 < 2147483647 ∧ 1471528627 < 2147483647); omega) canonical15 (by rfl)
#print axioms add15
theorem mul14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 824678393#u32 1340474354#u32 1436153629#u32 2013791478#u32) (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32)=ok (q 1974442451#u32 682073246#u32 1764368177#u32 1827528080#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (824678393 < 2147483647 ∧ 1340474354 < 2147483647) ∧ (1436153629 < 2147483647 ∧ 2013791478 < 2147483647); omega) (by change (1938229017 < 2147483647 ∧ 474903281 < 2147483647) ∧ (2119643323 < 2147483647 ∧ 1456121415 < 2147483647); omega) (by rfl)
#print axioms mul14
theorem add14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1974442451#u32 682073246#u32 1764368177#u32 1827528080#u32) c14=ok (q 1320941510#u32 154334066#u32 1332945878#u32 1627398046#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1974442451 < 2147483647 ∧ 682073246 < 2147483647) ∧ (1764368177 < 2147483647 ∧ 1827528080 < 2147483647); omega) canonical14 (by rfl)
#print axioms add14
def final : Q := (q 1320941510#u32 154334066#u32 1332945878#u32 1627398046#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 1#usize 28#usize initial 14#usize final := by
  refine .step (by change 28>0; omega) (JFr_IndexArithmetic.sub 28#usize 27#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32) from rfl) mul27 (show Array.index_usize p 27#usize=ok c27 from rfl) add27 ?_
  refine .step (by change 27>0; omega) (JFr_IndexArithmetic.sub 27#usize 26#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32) from rfl) mul26 (show Array.index_usize p 26#usize=ok c26 from rfl) add26 ?_
  refine .step (by change 26>0; omega) (JFr_IndexArithmetic.sub 26#usize 25#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32) from rfl) mul25 (show Array.index_usize p 25#usize=ok c25 from rfl) add25 ?_
  refine .step (by change 25>0; omega) (JFr_IndexArithmetic.sub 25#usize 24#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32) from rfl) mul24 (show Array.index_usize p 24#usize=ok c24 from rfl) add24 ?_
  refine .step (by change 24>0; omega) (JFr_IndexArithmetic.sub 24#usize 23#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32) from rfl) mul23 (show Array.index_usize p 23#usize=ok c23 from rfl) add23 ?_
  refine .step (by change 23>0; omega) (JFr_IndexArithmetic.sub 23#usize 22#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32) from rfl) mul22 (show Array.index_usize p 22#usize=ok c22 from rfl) add22 ?_
  refine .step (by change 22>0; omega) (JFr_IndexArithmetic.sub 22#usize 21#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32) from rfl) mul21 (show Array.index_usize p 21#usize=ok c21 from rfl) add21 ?_
  refine .step (by change 21>0; omega) (JFr_IndexArithmetic.sub 21#usize 20#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32) from rfl) mul20 (show Array.index_usize p 20#usize=ok c20 from rfl) add20 ?_
  refine .step (by change 20>0; omega) (JFr_IndexArithmetic.sub 20#usize 19#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32) from rfl) mul19 (show Array.index_usize p 19#usize=ok c19 from rfl) add19 ?_
  refine .step (by change 19>0; omega) (JFr_IndexArithmetic.sub 19#usize 18#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32) from rfl) mul18 (show Array.index_usize p 18#usize=ok c18 from rfl) add18 ?_
  refine .step (by change 18>0; omega) (JFr_IndexArithmetic.sub 18#usize 17#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32) from rfl) mul17 (show Array.index_usize p 17#usize=ok c17 from rfl) add17 ?_
  refine .step (by change 17>0; omega) (JFr_IndexArithmetic.sub 17#usize 16#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32) from rfl) mul16 (show Array.index_usize p 16#usize=ok c16 from rfl) add16 ?_
  refine .step (by change 16>0; omega) (JFr_IndexArithmetic.sub 16#usize 15#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32) from rfl) mul15 (show Array.index_usize p 15#usize=ok c15 from rfl) add15 ?_
  refine .step (by change 15>0; omega) (JFr_IndexArithmetic.sub 15#usize 14#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 1938229017#u32 474903281#u32 2119643323#u32 1456121415#u32) from rfl) mul14 (show Array.index_usize p 14#usize=ok c14 from rfl) add14 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner01_0
