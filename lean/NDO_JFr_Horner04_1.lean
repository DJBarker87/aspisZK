import NDO_JFr_Data04
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner04_1
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data04
def initial : Q := (q 632766064#u32 450267381#u32 531122620#u32 1261043823#u32)
theorem mul13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 632766064#u32 450267381#u32 531122620#u32 1261043823#u32) (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32)=ok (q 1932821200#u32 604428087#u32 25618600#u32 2120229453#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (632766064 < 2147483647 ∧ 450267381 < 2147483647) ∧ (531122620 < 2147483647 ∧ 1261043823 < 2147483647); omega) (by change (1106424694 < 2147483647 ∧ 342809735 < 2147483647) ∧ (1036886578 < 2147483647 ∧ 305075687 < 2147483647); omega) (by rfl)
#print axioms mul13
theorem add13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1932821200#u32 604428087#u32 25618600#u32 2120229453#u32) c13=ok (q 33190342#u32 282220918#u32 1533937163#u32 1732507802#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1932821200 < 2147483647 ∧ 604428087 < 2147483647) ∧ (25618600 < 2147483647 ∧ 2120229453 < 2147483647); omega) canonical13 (by rfl)
#print axioms add13
theorem mul12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 33190342#u32 282220918#u32 1533937163#u32 1732507802#u32) (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32)=ok (q 429912924#u32 296545700#u32 2038830409#u32 196927279#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (33190342 < 2147483647 ∧ 282220918 < 2147483647) ∧ (1533937163 < 2147483647 ∧ 1732507802 < 2147483647); omega) (by change (1106424694 < 2147483647 ∧ 342809735 < 2147483647) ∧ (1036886578 < 2147483647 ∧ 305075687 < 2147483647); omega) (by rfl)
#print axioms mul12
theorem add12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 429912924#u32 296545700#u32 2038830409#u32 196927279#u32) c12=ok (q 1140782445#u32 1581851046#u32 247373933#u32 178904966#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (429912924 < 2147483647 ∧ 296545700 < 2147483647) ∧ (2038830409 < 2147483647 ∧ 196927279 < 2147483647); omega) canonical12 (by rfl)
#print axioms add12
theorem mul11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1140782445#u32 1581851046#u32 247373933#u32 178904966#u32) (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32)=ok (q 835811278#u32 1525455546#u32 391303443#u32 2117877334#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1140782445 < 2147483647 ∧ 1581851046 < 2147483647) ∧ (247373933 < 2147483647 ∧ 178904966 < 2147483647); omega) (by change (1106424694 < 2147483647 ∧ 342809735 < 2147483647) ∧ (1036886578 < 2147483647 ∧ 305075687 < 2147483647); omega) (by rfl)
#print axioms mul11
theorem add11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 835811278#u32 1525455546#u32 391303443#u32 2117877334#u32) c11=ok (q 707683104#u32 2055956157#u32 411836275#u32 1326164777#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (835811278 < 2147483647 ∧ 1525455546 < 2147483647) ∧ (391303443 < 2147483647 ∧ 2117877334 < 2147483647); omega) canonical11 (by rfl)
#print axioms add11
theorem mul10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 707683104#u32 2055956157#u32 411836275#u32 1326164777#u32) (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32)=ok (q 2108215601#u32 626245682#u32 870935250#u32 1567097716#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (707683104 < 2147483647 ∧ 2055956157 < 2147483647) ∧ (411836275 < 2147483647 ∧ 1326164777 < 2147483647); omega) (by change (1106424694 < 2147483647 ∧ 342809735 < 2147483647) ∧ (1036886578 < 2147483647 ∧ 305075687 < 2147483647); omega) (by rfl)
#print axioms mul10
theorem add10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2108215601#u32 626245682#u32 870935250#u32 1567097716#u32) c10=ok (q 1375107302#u32 1440220545#u32 2016379659#u32 1521123071#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2108215601 < 2147483647 ∧ 626245682 < 2147483647) ∧ (870935250 < 2147483647 ∧ 1567097716 < 2147483647); omega) canonical10 (by rfl)
#print axioms add10
theorem mul09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1375107302#u32 1440220545#u32 2016379659#u32 1521123071#u32) (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32)=ok (q 198378001#u32 1831651948#u32 400989660#u32 1297726796#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1375107302 < 2147483647 ∧ 1440220545 < 2147483647) ∧ (2016379659 < 2147483647 ∧ 1521123071 < 2147483647); omega) (by change (1106424694 < 2147483647 ∧ 342809735 < 2147483647) ∧ (1036886578 < 2147483647 ∧ 305075687 < 2147483647); omega) (by rfl)
#print axioms mul09
theorem add09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 198378001#u32 1831651948#u32 400989660#u32 1297726796#u32) c09=ok (q 2105594259#u32 1410347558#u32 10429260#u32 1765075980#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (198378001 < 2147483647 ∧ 1831651948 < 2147483647) ∧ (400989660 < 2147483647 ∧ 1297726796 < 2147483647); omega) canonical09 (by rfl)
#print axioms add09
theorem mul08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2105594259#u32 1410347558#u32 10429260#u32 1765075980#u32) (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32)=ok (q 488643535#u32 429649280#u32 1475256065#u32 1378480142#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2105594259 < 2147483647 ∧ 1410347558 < 2147483647) ∧ (10429260 < 2147483647 ∧ 1765075980 < 2147483647); omega) (by change (1106424694 < 2147483647 ∧ 342809735 < 2147483647) ∧ (1036886578 < 2147483647 ∧ 305075687 < 2147483647); omega) (by rfl)
#print axioms mul08
theorem add08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 488643535#u32 429649280#u32 1475256065#u32 1378480142#u32) c08=ok (q 984151393#u32 190070622#u32 1814479663#u32 1842725768#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (488643535 < 2147483647 ∧ 429649280 < 2147483647) ∧ (1475256065 < 2147483647 ∧ 1378480142 < 2147483647); omega) canonical08 (by rfl)
#print axioms add08
theorem mul07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 984151393#u32 190070622#u32 1814479663#u32 1842725768#u32) (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32)=ok (q 1824787295#u32 270189569#u32 2113157555#u32 85000192#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (984151393 < 2147483647 ∧ 190070622 < 2147483647) ∧ (1814479663 < 2147483647 ∧ 1842725768 < 2147483647); omega) (by change (1106424694 < 2147483647 ∧ 342809735 < 2147483647) ∧ (1036886578 < 2147483647 ∧ 305075687 < 2147483647); omega) (by rfl)
#print axioms mul07
theorem add07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1824787295#u32 270189569#u32 2113157555#u32 85000192#u32) c07=ok (q 1340619325#u32 1826132763#u32 1715749048#u32 1044172579#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1824787295 < 2147483647 ∧ 270189569 < 2147483647) ∧ (2113157555 < 2147483647 ∧ 85000192 < 2147483647); omega) canonical07 (by rfl)
#print axioms add07
theorem mul06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1340619325#u32 1826132763#u32 1715749048#u32 1044172579#u32) (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32)=ok (q 2139233380#u32 354412470#u32 201648242#u32 1232393184#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1340619325 < 2147483647 ∧ 1826132763 < 2147483647) ∧ (1715749048 < 2147483647 ∧ 1044172579 < 2147483647); omega) (by change (1106424694 < 2147483647 ∧ 342809735 < 2147483647) ∧ (1036886578 < 2147483647 ∧ 305075687 < 2147483647); omega) (by rfl)
#print axioms mul06
theorem add06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2139233380#u32 354412470#u32 201648242#u32 1232393184#u32) c06=ok (q 1985323276#u32 1713165147#u32 1208791891#u32 758115648#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2139233380 < 2147483647 ∧ 354412470 < 2147483647) ∧ (201648242 < 2147483647 ∧ 1232393184 < 2147483647); omega) canonical06 (by rfl)
#print axioms add06
theorem mul05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1985323276#u32 1713165147#u32 1208791891#u32 758115648#u32) (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32)=ok (q 731709811#u32 101609250#u32 1808084679#u32 164032001#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1985323276 < 2147483647 ∧ 1713165147 < 2147483647) ∧ (1208791891 < 2147483647 ∧ 758115648 < 2147483647); omega) (by change (1106424694 < 2147483647 ∧ 342809735 < 2147483647) ∧ (1036886578 < 2147483647 ∧ 305075687 < 2147483647); omega) (by rfl)
#print axioms mul05
theorem add05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 731709811#u32 101609250#u32 1808084679#u32 164032001#u32) c05=ok (q 1087344344#u32 198400876#u32 1191350229#u32 262765197#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (731709811 < 2147483647 ∧ 101609250 < 2147483647) ∧ (1808084679 < 2147483647 ∧ 164032001 < 2147483647); omega) canonical05 (by rfl)
#print axioms add05
theorem mul04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1087344344#u32 198400876#u32 1191350229#u32 262765197#u32) (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32)=ok (q 1408297500#u32 436864504#u32 912361050#u32 86913892#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1087344344 < 2147483647 ∧ 198400876 < 2147483647) ∧ (1191350229 < 2147483647 ∧ 262765197 < 2147483647); omega) (by change (1106424694 < 2147483647 ∧ 342809735 < 2147483647) ∧ (1036886578 < 2147483647 ∧ 305075687 < 2147483647); omega) (by rfl)
#print axioms mul04
theorem add04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1408297500#u32 436864504#u32 912361050#u32 86913892#u32) c04=ok (q 1752547471#u32 989153046#u32 691599618#u32 1518590230#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1408297500 < 2147483647 ∧ 436864504 < 2147483647) ∧ (912361050 < 2147483647 ∧ 86913892 < 2147483647); omega) canonical04 (by rfl)
#print axioms add04
theorem mul03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1752547471#u32 989153046#u32 691599618#u32 1518590230#u32) (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32)=ok (q 2016131281#u32 791461725#u32 683526850#u32 697731953#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1752547471 < 2147483647 ∧ 989153046 < 2147483647) ∧ (691599618 < 2147483647 ∧ 1518590230 < 2147483647); omega) (by change (1106424694 < 2147483647 ∧ 342809735 < 2147483647) ∧ (1036886578 < 2147483647 ∧ 305075687 < 2147483647); omega) (by rfl)
#print axioms mul03
theorem add03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2016131281#u32 791461725#u32 683526850#u32 697731953#u32) c03=ok (q 2123057319#u32 670750605#u32 1720581319#u32 329133244#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2016131281 < 2147483647 ∧ 791461725 < 2147483647) ∧ (683526850 < 2147483647 ∧ 697731953 < 2147483647); omega) canonical03 (by rfl)
#print axioms add03
theorem mul02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2123057319#u32 670750605#u32 1720581319#u32 329133244#u32) (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32)=ok (q 438337730#u32 2085435455#u32 1909184930#u32 518219889#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2123057319 < 2147483647 ∧ 670750605 < 2147483647) ∧ (1720581319 < 2147483647 ∧ 329133244 < 2147483647); omega) (by change (1106424694 < 2147483647 ∧ 342809735 < 2147483647) ∧ (1036886578 < 2147483647 ∧ 305075687 < 2147483647); omega) (by rfl)
#print axioms mul02
theorem add02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 438337730#u32 2085435455#u32 1909184930#u32 518219889#u32) c02=ok (q 730341451#u32 736362936#u32 832963154#u32 477874341#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (438337730 < 2147483647 ∧ 2085435455 < 2147483647) ∧ (1909184930 < 2147483647 ∧ 518219889 < 2147483647); omega) canonical02 (by rfl)
#print axioms add02
theorem mul01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 730341451#u32 736362936#u32 832963154#u32 477874341#u32) (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32)=ok (q 1976568193#u32 1591228485#u32 1833562967#u32 1800060647#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (730341451 < 2147483647 ∧ 736362936 < 2147483647) ∧ (832963154 < 2147483647 ∧ 477874341 < 2147483647); omega) (by change (1106424694 < 2147483647 ∧ 342809735 < 2147483647) ∧ (1036886578 < 2147483647 ∧ 305075687 < 2147483647); omega) (by rfl)
#print axioms mul01
theorem add01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1976568193#u32 1591228485#u32 1833562967#u32 1800060647#u32) c01=ok (q 155767663#u32 32224758#u32 829240520#u32 1327566383#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1976568193 < 2147483647 ∧ 1591228485 < 2147483647) ∧ (1833562967 < 2147483647 ∧ 1800060647 < 2147483647); omega) canonical01 (by rfl)
#print axioms add01
theorem mul00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 155767663#u32 32224758#u32 829240520#u32 1327566383#u32) (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32)=ok (q 1263839472#u32 979131171#u32 1588115050#u32 788331251#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (155767663 < 2147483647 ∧ 32224758 < 2147483647) ∧ (829240520 < 2147483647 ∧ 1327566383 < 2147483647); omega) (by change (1106424694 < 2147483647 ∧ 342809735 < 2147483647) ∧ (1036886578 < 2147483647 ∧ 305075687 < 2147483647); omega) (by rfl)
#print axioms mul00
theorem add00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1263839472#u32 979131171#u32 1588115050#u32 788331251#u32) c00=ok (q 1050243242#u32 1080496664#u32 1505465875#u32 28808746#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1263839472 < 2147483647 ∧ 979131171 < 2147483647) ∧ (1588115050 < 2147483647 ∧ 788331251 < 2147483647); omega) canonical00 (by rfl)
#print axioms add00
def final : Q := (q 1050243242#u32 1080496664#u32 1505465875#u32 28808746#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 4#usize 14#usize initial 0#usize final := by
  refine .step (by change 14>0; omega) (JFr_IndexArithmetic.sub 14#usize 13#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32) from rfl) mul13 (show Array.index_usize p 13#usize=ok c13 from rfl) add13 ?_
  refine .step (by change 13>0; omega) (JFr_IndexArithmetic.sub 13#usize 12#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32) from rfl) mul12 (show Array.index_usize p 12#usize=ok c12 from rfl) add12 ?_
  refine .step (by change 12>0; omega) (JFr_IndexArithmetic.sub 12#usize 11#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32) from rfl) mul11 (show Array.index_usize p 11#usize=ok c11 from rfl) add11 ?_
  refine .step (by change 11>0; omega) (JFr_IndexArithmetic.sub 11#usize 10#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32) from rfl) mul10 (show Array.index_usize p 10#usize=ok c10 from rfl) add10 ?_
  refine .step (by change 10>0; omega) (JFr_IndexArithmetic.sub 10#usize 9#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32) from rfl) mul09 (show Array.index_usize p 9#usize=ok c09 from rfl) add09 ?_
  refine .step (by change 9>0; omega) (JFr_IndexArithmetic.sub 9#usize 8#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32) from rfl) mul08 (show Array.index_usize p 8#usize=ok c08 from rfl) add08 ?_
  refine .step (by change 8>0; omega) (JFr_IndexArithmetic.sub 8#usize 7#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32) from rfl) mul07 (show Array.index_usize p 7#usize=ok c07 from rfl) add07 ?_
  refine .step (by change 7>0; omega) (JFr_IndexArithmetic.sub 7#usize 6#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32) from rfl) mul06 (show Array.index_usize p 6#usize=ok c06 from rfl) add06 ?_
  refine .step (by change 6>0; omega) (JFr_IndexArithmetic.sub 6#usize 5#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32) from rfl) mul05 (show Array.index_usize p 5#usize=ok c05 from rfl) add05 ?_
  refine .step (by change 5>0; omega) (JFr_IndexArithmetic.sub 5#usize 4#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32) from rfl) mul04 (show Array.index_usize p 4#usize=ok c04 from rfl) add04 ?_
  refine .step (by change 4>0; omega) (JFr_IndexArithmetic.sub 4#usize 3#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32) from rfl) mul03 (show Array.index_usize p 3#usize=ok c03 from rfl) add03 ?_
  refine .step (by change 3>0; omega) (JFr_IndexArithmetic.sub 3#usize 2#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32) from rfl) mul02 (show Array.index_usize p 2#usize=ok c02 from rfl) add02 ?_
  refine .step (by change 2>0; omega) (JFr_IndexArithmetic.sub 2#usize 1#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32) from rfl) mul01 (show Array.index_usize p 1#usize=ok c01 from rfl) add01 ?_
  refine .step (by change 1>0; omega) (JFr_IndexArithmetic.sub 1#usize 0#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32) from rfl) mul00 (show Array.index_usize p 0#usize=ok c00 from rfl) add00 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner04_1
