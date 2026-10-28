import NDO_JFr_Data08
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner08_0
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data08
def initial : Q := (q 0#u32 0#u32 0#u32 0#u32)
theorem mul27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 0#u32 0#u32 0#u32 0#u32) (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32)=ok (q 0#u32 0#u32 0#u32 0#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) (by change (454398981 < 2147483647 ∧ 504493626 < 2147483647) ∧ (2008082900 < 2147483647 ∧ 1252680230 < 2147483647); omega) (by rfl)
#print axioms mul27
theorem add27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 0#u32 0#u32 0#u32 0#u32) c27=ok (q 1591121890#u32 675869899#u32 158959062#u32 158130071#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) canonical27 (by rfl)
#print axioms add27
theorem mul26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1591121890#u32 675869899#u32 158959062#u32 158130071#u32) (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32)=ok (q 1921285691#u32 608678326#u32 531901526#u32 2133940165#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1591121890 < 2147483647 ∧ 675869899 < 2147483647) ∧ (158959062 < 2147483647 ∧ 158130071 < 2147483647); omega) (by change (454398981 < 2147483647 ∧ 504493626 < 2147483647) ∧ (2008082900 < 2147483647 ∧ 1252680230 < 2147483647); omega) (by rfl)
#print axioms mul26
theorem add26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1921285691#u32 608678326#u32 531901526#u32 2133940165#u32) c26=ok (q 1813547468#u32 40933478#u32 1263459082#u32 2107408171#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1921285691 < 2147483647 ∧ 608678326 < 2147483647) ∧ (531901526 < 2147483647 ∧ 2133940165 < 2147483647); omega) canonical26 (by rfl)
#print axioms add26
theorem mul25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1813547468#u32 40933478#u32 1263459082#u32 2107408171#u32) (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32)=ok (q 107333178#u32 2118884135#u32 1522725134#u32 2057865059#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1813547468 < 2147483647 ∧ 40933478 < 2147483647) ∧ (1263459082 < 2147483647 ∧ 2107408171 < 2147483647); omega) (by change (454398981 < 2147483647 ∧ 504493626 < 2147483647) ∧ (2008082900 < 2147483647 ∧ 1252680230 < 2147483647); omega) (by rfl)
#print axioms mul25
theorem add25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 107333178#u32 2118884135#u32 1522725134#u32 2057865059#u32) c25=ok (q 196092015#u32 991458405#u32 493934203#u32 1368171175#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (107333178 < 2147483647 ∧ 2118884135 < 2147483647) ∧ (1522725134 < 2147483647 ∧ 2057865059 < 2147483647); omega) canonical25 (by rfl)
#print axioms add25
theorem mul24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 196092015#u32 991458405#u32 493934203#u32 1368171175#u32) (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32)=ok (q 1439264996#u32 1349579178#u32 2147442487#u32 1702226750#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (196092015 < 2147483647 ∧ 991458405 < 2147483647) ∧ (493934203 < 2147483647 ∧ 1368171175 < 2147483647); omega) (by change (454398981 < 2147483647 ∧ 504493626 < 2147483647) ∧ (2008082900 < 2147483647 ∧ 1252680230 < 2147483647); omega) (by rfl)
#print axioms mul24
theorem add24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1439264996#u32 1349579178#u32 2147442487#u32 1702226750#u32) c24=ok (q 661033523#u32 1213571648#u32 470395522#u32 247428458#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1439264996 < 2147483647 ∧ 1349579178 < 2147483647) ∧ (2147442487 < 2147483647 ∧ 1702226750 < 2147483647); omega) canonical24 (by rfl)
#print axioms add24
theorem mul23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 661033523#u32 1213571648#u32 470395522#u32 247428458#u32) (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32)=ok (q 2128473803#u32 1724200596#u32 957073113#u32 1962303282#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (661033523 < 2147483647 ∧ 1213571648 < 2147483647) ∧ (470395522 < 2147483647 ∧ 247428458 < 2147483647); omega) (by change (454398981 < 2147483647 ∧ 504493626 < 2147483647) ∧ (2008082900 < 2147483647 ∧ 1252680230 < 2147483647); omega) (by rfl)
#print axioms mul23
theorem add23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2128473803#u32 1724200596#u32 957073113#u32 1962303282#u32) c23=ok (q 1823870939#u32 895509359#u32 394448134#u32 785964892#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2128473803 < 2147483647 ∧ 1724200596 < 2147483647) ∧ (957073113 < 2147483647 ∧ 1962303282 < 2147483647); omega) canonical23 (by rfl)
#print axioms add23
theorem mul22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1823870939#u32 895509359#u32 394448134#u32 785964892#u32) (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32)=ok (q 28122817#u32 1180112264#u32 635276805#u32 920733163#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1823870939 < 2147483647 ∧ 895509359 < 2147483647) ∧ (394448134 < 2147483647 ∧ 785964892 < 2147483647); omega) (by change (454398981 < 2147483647 ∧ 504493626 < 2147483647) ∧ (2008082900 < 2147483647 ∧ 1252680230 < 2147483647); omega) (by rfl)
#print axioms mul22
theorem add22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 28122817#u32 1180112264#u32 635276805#u32 920733163#u32) c22=ok (q 1046830459#u32 243264754#u32 1425495272#u32 747307593#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (28122817 < 2147483647 ∧ 1180112264 < 2147483647) ∧ (635276805 < 2147483647 ∧ 920733163 < 2147483647); omega) canonical22 (by rfl)
#print axioms add22
theorem mul21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1046830459#u32 243264754#u32 1425495272#u32 747307593#u32) (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32)=ok (q 393462339#u32 1725695911#u32 1627426113#u32 887174868#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1046830459 < 2147483647 ∧ 243264754 < 2147483647) ∧ (1425495272 < 2147483647 ∧ 747307593 < 2147483647); omega) (by change (454398981 < 2147483647 ∧ 504493626 < 2147483647) ∧ (2008082900 < 2147483647 ∧ 1252680230 < 2147483647); omega) (by rfl)
#print axioms mul21
theorem add21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 393462339#u32 1725695911#u32 1627426113#u32 887174868#u32) c21=ok (q 234212238#u32 478271431#u32 254986049#u32 1786710280#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (393462339 < 2147483647 ∧ 1725695911 < 2147483647) ∧ (1627426113 < 2147483647 ∧ 887174868 < 2147483647); omega) canonical21 (by rfl)
#print axioms add21
theorem mul20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 234212238#u32 478271431#u32 254986049#u32 1786710280#u32) (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32)=ok (q 1395272958#u32 1558418246#u32 2106634305#u32 1945984866#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (234212238 < 2147483647 ∧ 478271431 < 2147483647) ∧ (254986049 < 2147483647 ∧ 1786710280 < 2147483647); omega) (by change (454398981 < 2147483647 ∧ 504493626 < 2147483647) ∧ (2008082900 < 2147483647 ∧ 1252680230 < 2147483647); omega) (by rfl)
#print axioms mul20
theorem add20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1395272958#u32 1558418246#u32 2106634305#u32 1945984866#u32) c20=ok (q 1698474186#u32 1778949176#u32 1648957617#u32 985303450#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1395272958 < 2147483647 ∧ 1558418246 < 2147483647) ∧ (2106634305 < 2147483647 ∧ 1945984866 < 2147483647); omega) canonical20 (by rfl)
#print axioms add20
theorem mul19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1698474186#u32 1778949176#u32 1648957617#u32 985303450#u32) (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32)=ok (q 181241019#u32 1203259407#u32 1338564763#u32 2015997215#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1698474186 < 2147483647 ∧ 1778949176 < 2147483647) ∧ (1648957617 < 2147483647 ∧ 985303450 < 2147483647); omega) (by change (454398981 < 2147483647 ∧ 504493626 < 2147483647) ∧ (2008082900 < 2147483647 ∧ 1252680230 < 2147483647); omega) (by rfl)
#print axioms mul19
theorem add19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 181241019#u32 1203259407#u32 1338564763#u32 2015997215#u32) c19=ok (q 610741328#u32 837345915#u32 115349634#u32 1542467241#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (181241019 < 2147483647 ∧ 1203259407 < 2147483647) ∧ (1338564763 < 2147483647 ∧ 2015997215 < 2147483647); omega) canonical19 (by rfl)
#print axioms add19
theorem mul18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 610741328#u32 837345915#u32 115349634#u32 1542467241#u32) (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32)=ok (q 515649614#u32 189513145#u32 39247230#u32 157944395#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (610741328 < 2147483647 ∧ 837345915 < 2147483647) ∧ (115349634 < 2147483647 ∧ 1542467241 < 2147483647); omega) (by change (454398981 < 2147483647 ∧ 504493626 < 2147483647) ∧ (2008082900 < 2147483647 ∧ 1252680230 < 2147483647); omega) (by rfl)
#print axioms mul18
theorem add18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 515649614#u32 189513145#u32 39247230#u32 157944395#u32) c18=ok (q 1733749348#u32 1154470447#u32 366795986#u32 1936490624#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (515649614 < 2147483647 ∧ 189513145 < 2147483647) ∧ (39247230 < 2147483647 ∧ 157944395 < 2147483647); omega) canonical18 (by rfl)
#print axioms add18
theorem mul17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1733749348#u32 1154470447#u32 366795986#u32 1936490624#u32) (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32)=ok (q 1104211630#u32 40792233#u32 1898844769#u32 1023773547#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1733749348 < 2147483647 ∧ 1154470447 < 2147483647) ∧ (366795986 < 2147483647 ∧ 1936490624 < 2147483647); omega) (by change (454398981 < 2147483647 ∧ 504493626 < 2147483647) ∧ (2008082900 < 2147483647 ∧ 1252680230 < 2147483647); omega) (by rfl)
#print axioms mul17
theorem add17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1104211630#u32 40792233#u32 1898844769#u32 1023773547#u32) c17=ok (q 249243203#u32 378328955#u32 144929171#u32 134439760#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1104211630 < 2147483647 ∧ 40792233 < 2147483647) ∧ (1898844769 < 2147483647 ∧ 1023773547 < 2147483647); omega) canonical17 (by rfl)
#print axioms add17
theorem mul16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 249243203#u32 378328955#u32 144929171#u32 134439760#u32) (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32)=ok (q 312089808#u32 708894946#u32 1046496438#u32 728764451#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (249243203 < 2147483647 ∧ 378328955 < 2147483647) ∧ (144929171 < 2147483647 ∧ 134439760 < 2147483647); omega) (by change (454398981 < 2147483647 ∧ 504493626 < 2147483647) ∧ (2008082900 < 2147483647 ∧ 1252680230 < 2147483647); omega) (by rfl)
#print axioms mul16
theorem add16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 312089808#u32 708894946#u32 1046496438#u32 728764451#u32) c16=ok (q 411070960#u32 210494983#u32 143471214#u32 1591513728#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (312089808 < 2147483647 ∧ 708894946 < 2147483647) ∧ (1046496438 < 2147483647 ∧ 728764451 < 2147483647); omega) canonical16 (by rfl)
#print axioms add16
theorem mul15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 411070960#u32 210494983#u32 143471214#u32 1591513728#u32) (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32)=ok (q 1471025482#u32 1501939826#u32 1013335380#u32 1702017545#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (411070960 < 2147483647 ∧ 210494983 < 2147483647) ∧ (143471214 < 2147483647 ∧ 1591513728 < 2147483647); omega) (by change (454398981 < 2147483647 ∧ 504493626 < 2147483647) ∧ (2008082900 < 2147483647 ∧ 1252680230 < 2147483647); omega) (by rfl)
#print axioms mul15
theorem add15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1471025482#u32 1501939826#u32 1013335380#u32 1702017545#u32) c15=ok (q 1487698552#u32 803851147#u32 168686194#u32 928007895#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1471025482 < 2147483647 ∧ 1501939826 < 2147483647) ∧ (1013335380 < 2147483647 ∧ 1702017545 < 2147483647); omega) canonical15 (by rfl)
#print axioms add15
theorem mul14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1487698552#u32 803851147#u32 168686194#u32 928007895#u32) (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32)=ok (q 1184855512#u32 522400907#u32 892943290#u32 1158650916#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1487698552 < 2147483647 ∧ 803851147 < 2147483647) ∧ (168686194 < 2147483647 ∧ 928007895 < 2147483647); omega) (by change (454398981 < 2147483647 ∧ 504493626 < 2147483647) ∧ (2008082900 < 2147483647 ∧ 1252680230 < 2147483647); omega) (by rfl)
#print axioms mul14
theorem add14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1184855512#u32 522400907#u32 892943290#u32 1158650916#u32) c14=ok (q 73961802#u32 2037623854#u32 1790073501#u32 1355316080#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1184855512 < 2147483647 ∧ 522400907 < 2147483647) ∧ (892943290 < 2147483647 ∧ 1158650916 < 2147483647); omega) canonical14 (by rfl)
#print axioms add14
def final : Q := (q 73961802#u32 2037623854#u32 1790073501#u32 1355316080#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 8#usize 28#usize initial 14#usize final := by
  refine .step (by change 28>0; omega) (JFr_IndexArithmetic.sub 28#usize 27#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32) from rfl) mul27 (show Array.index_usize p 27#usize=ok c27 from rfl) add27 ?_
  refine .step (by change 27>0; omega) (JFr_IndexArithmetic.sub 27#usize 26#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32) from rfl) mul26 (show Array.index_usize p 26#usize=ok c26 from rfl) add26 ?_
  refine .step (by change 26>0; omega) (JFr_IndexArithmetic.sub 26#usize 25#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32) from rfl) mul25 (show Array.index_usize p 25#usize=ok c25 from rfl) add25 ?_
  refine .step (by change 25>0; omega) (JFr_IndexArithmetic.sub 25#usize 24#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32) from rfl) mul24 (show Array.index_usize p 24#usize=ok c24 from rfl) add24 ?_
  refine .step (by change 24>0; omega) (JFr_IndexArithmetic.sub 24#usize 23#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32) from rfl) mul23 (show Array.index_usize p 23#usize=ok c23 from rfl) add23 ?_
  refine .step (by change 23>0; omega) (JFr_IndexArithmetic.sub 23#usize 22#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32) from rfl) mul22 (show Array.index_usize p 22#usize=ok c22 from rfl) add22 ?_
  refine .step (by change 22>0; omega) (JFr_IndexArithmetic.sub 22#usize 21#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32) from rfl) mul21 (show Array.index_usize p 21#usize=ok c21 from rfl) add21 ?_
  refine .step (by change 21>0; omega) (JFr_IndexArithmetic.sub 21#usize 20#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32) from rfl) mul20 (show Array.index_usize p 20#usize=ok c20 from rfl) add20 ?_
  refine .step (by change 20>0; omega) (JFr_IndexArithmetic.sub 20#usize 19#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32) from rfl) mul19 (show Array.index_usize p 19#usize=ok c19 from rfl) add19 ?_
  refine .step (by change 19>0; omega) (JFr_IndexArithmetic.sub 19#usize 18#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32) from rfl) mul18 (show Array.index_usize p 18#usize=ok c18 from rfl) add18 ?_
  refine .step (by change 18>0; omega) (JFr_IndexArithmetic.sub 18#usize 17#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32) from rfl) mul17 (show Array.index_usize p 17#usize=ok c17 from rfl) add17 ?_
  refine .step (by change 17>0; omega) (JFr_IndexArithmetic.sub 17#usize 16#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32) from rfl) mul16 (show Array.index_usize p 16#usize=ok c16 from rfl) add16 ?_
  refine .step (by change 16>0; omega) (JFr_IndexArithmetic.sub 16#usize 15#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32) from rfl) mul15 (show Array.index_usize p 15#usize=ok c15 from rfl) add15 ?_
  refine .step (by change 15>0; omega) (JFr_IndexArithmetic.sub 15#usize 14#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32) from rfl) mul14 (show Array.index_usize p 14#usize=ok c14 from rfl) add14 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner08_0
