import NDO_JFr_Data04
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner04_1
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data04
def initial : Q := (q 1718921177#u32 777043832#u32 776900213#u32 1727828662#u32)
theorem mul13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1718921177#u32 777043832#u32 776900213#u32 1727828662#u32) (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32)=ok (q 1601034720#u32 1472315151#u32 862458632#u32 1505470326#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1718921177 < 2147483647 ∧ 777043832 < 2147483647) ∧ (776900213 < 2147483647 ∧ 1727828662 < 2147483647); omega) (by change (763754670 < 2147483647 ∧ 31463458 < 2147483647) ∧ (1727849165 < 2147483647 ∧ 1028580563 < 2147483647); omega) (by rfl)
#print axioms mul13
theorem add13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1601034720#u32 1472315151#u32 862458632#u32 1505470326#u32) c13=ok (q 1591420069#u32 47442291#u32 1286363889#u32 1163774578#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1601034720 < 2147483647 ∧ 1472315151 < 2147483647) ∧ (862458632 < 2147483647 ∧ 1505470326 < 2147483647); omega) canonical13 (by rfl)
#print axioms add13
theorem mul12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1591420069#u32 47442291#u32 1286363889#u32 1163774578#u32) (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32)=ok (q 225986657#u32 956909834#u32 589355394#u32 728291220#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1591420069 < 2147483647 ∧ 47442291 < 2147483647) ∧ (1286363889 < 2147483647 ∧ 1163774578 < 2147483647); omega) (by change (763754670 < 2147483647 ∧ 31463458 < 2147483647) ∧ (1727849165 < 2147483647 ∧ 1028580563 < 2147483647); omega) (by rfl)
#print axioms mul12
theorem add12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 225986657#u32 956909834#u32 589355394#u32 728291220#u32) c12=ok (q 1287640030#u32 294187371#u32 1086586348#u32 1657471179#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (225986657 < 2147483647 ∧ 956909834 < 2147483647) ∧ (589355394 < 2147483647 ∧ 728291220 < 2147483647); omega) canonical12 (by rfl)
#print axioms add12
theorem mul11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1287640030#u32 294187371#u32 1086586348#u32 1657471179#u32) (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32)=ok (q 84596474#u32 1027078525#u32 1254687365#u32 403659375#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1287640030 < 2147483647 ∧ 294187371 < 2147483647) ∧ (1086586348 < 2147483647 ∧ 1657471179 < 2147483647); omega) (by change (763754670 < 2147483647 ∧ 31463458 < 2147483647) ∧ (1727849165 < 2147483647 ∧ 1028580563 < 2147483647); omega) (by rfl)
#print axioms mul11
theorem add11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 84596474#u32 1027078525#u32 1254687365#u32 403659375#u32) c11=ok (q 161198962#u32 1568078817#u32 2087396172#u32 1451810490#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (84596474 < 2147483647 ∧ 1027078525 < 2147483647) ∧ (1254687365 < 2147483647 ∧ 403659375 < 2147483647); omega) canonical11 (by rfl)
#print axioms add11
theorem mul10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 161198962#u32 1568078817#u32 2087396172#u32 1451810490#u32) (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32)=ok (q 475888018#u32 1574722596#u32 2097152408#u32 1776359594#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (161198962 < 2147483647 ∧ 1568078817 < 2147483647) ∧ (2087396172 < 2147483647 ∧ 1451810490 < 2147483647); omega) (by change (763754670 < 2147483647 ∧ 31463458 < 2147483647) ∧ (1727849165 < 2147483647 ∧ 1028580563 < 2147483647); omega) (by rfl)
#print axioms mul10
theorem add10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 475888018#u32 1574722596#u32 2097152408#u32 1776359594#u32) c10=ok (q 1429600843#u32 1256502745#u32 527260438#u32 1184223101#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (475888018 < 2147483647 ∧ 1574722596 < 2147483647) ∧ (2097152408 < 2147483647 ∧ 1776359594 < 2147483647); omega) canonical10 (by rfl)
#print axioms add10
theorem mul09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1429600843#u32 1256502745#u32 527260438#u32 1184223101#u32) (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32)=ok (q 1183825864#u32 742183535#u32 1334394099#u32 1581609628#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1429600843 < 2147483647 ∧ 1256502745 < 2147483647) ∧ (527260438 < 2147483647 ∧ 1184223101 < 2147483647); omega) (by change (763754670 < 2147483647 ∧ 31463458 < 2147483647) ∧ (1727849165 < 2147483647 ∧ 1028580563 < 2147483647); omega) (by rfl)
#print axioms mul09
theorem add09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1183825864#u32 742183535#u32 1334394099#u32 1581609628#u32) c09=ok (q 247965316#u32 1204404113#u32 1891278932#u32 891812988#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1183825864 < 2147483647 ∧ 742183535 < 2147483647) ∧ (1334394099 < 2147483647 ∧ 1581609628 < 2147483647); omega) canonical09 (by rfl)
#print axioms add09
theorem mul08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 247965316#u32 1204404113#u32 1891278932#u32 891812988#u32) (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32)=ok (q 919911761#u32 1235098848#u32 652355715#u32 1617198213#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (247965316 < 2147483647 ∧ 1204404113 < 2147483647) ∧ (1891278932 < 2147483647 ∧ 891812988 < 2147483647); omega) (by change (763754670 < 2147483647 ∧ 31463458 < 2147483647) ∧ (1727849165 < 2147483647 ∧ 1028580563 < 2147483647); omega) (by rfl)
#print axioms mul08
theorem add08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 919911761#u32 1235098848#u32 652355715#u32 1617198213#u32) c08=ok (q 1813919409#u32 777177939#u32 1676540588#u32 1633628377#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (919911761 < 2147483647 ∧ 1235098848 < 2147483647) ∧ (652355715 < 2147483647 ∧ 1617198213 < 2147483647); omega) canonical08 (by rfl)
#print axioms add08
theorem mul07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1813919409#u32 777177939#u32 1676540588#u32 1633628377#u32) (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32)=ok (q 1599121137#u32 323010311#u32 1440575261#u32 1150246674#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1813919409 < 2147483647 ∧ 777177939 < 2147483647) ∧ (1676540588 < 2147483647 ∧ 1633628377 < 2147483647); omega) (by change (763754670 < 2147483647 ∧ 31463458 < 2147483647) ∧ (1727849165 < 2147483647 ∧ 1028580563 < 2147483647); omega) (by rfl)
#print axioms mul07
theorem add07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1599121137#u32 323010311#u32 1440575261#u32 1150246674#u32) c07=ok (q 1743896918#u32 615411162#u32 1030328222#u32 1983408819#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1599121137 < 2147483647 ∧ 323010311 < 2147483647) ∧ (1440575261 < 2147483647 ∧ 1150246674 < 2147483647); omega) canonical07 (by rfl)
#print axioms add07
theorem mul06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1743896918#u32 615411162#u32 1030328222#u32 1983408819#u32) (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32)=ok (q 612060646#u32 1529837770#u32 1793786987#u32 1972819600#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1743896918 < 2147483647 ∧ 615411162 < 2147483647) ∧ (1030328222 < 2147483647 ∧ 1983408819 < 2147483647); omega) (by change (763754670 < 2147483647 ∧ 31463458 < 2147483647) ∧ (1727849165 < 2147483647 ∧ 1028580563 < 2147483647); omega) (by rfl)
#print axioms mul06
theorem add06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 612060646#u32 1529837770#u32 1793786987#u32 1972819600#u32) c06=ok (q 1992184755#u32 1896145875#u32 1442222163#u32 1486620752#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (612060646 < 2147483647 ∧ 1529837770 < 2147483647) ∧ (1793786987 < 2147483647 ∧ 1972819600 < 2147483647); omega) canonical06 (by rfl)
#print axioms add06
theorem mul05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1992184755#u32 1896145875#u32 1442222163#u32 1486620752#u32) (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32)=ok (q 2007018375#u32 760723424#u32 1174066059#u32 1289376128#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1992184755 < 2147483647 ∧ 1896145875 < 2147483647) ∧ (1442222163 < 2147483647 ∧ 1486620752 < 2147483647); omega) (by change (763754670 < 2147483647 ∧ 31463458 < 2147483647) ∧ (1727849165 < 2147483647 ∧ 1028580563 < 2147483647); omega) (by rfl)
#print axioms mul05
theorem add05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2007018375#u32 760723424#u32 1174066059#u32 1289376128#u32) c05=ok (q 803011521#u32 905020638#u32 1745802776#u32 762859377#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2007018375 < 2147483647 ∧ 760723424 < 2147483647) ∧ (1174066059 < 2147483647 ∧ 1289376128 < 2147483647); omega) canonical05 (by rfl)
#print axioms add05
theorem mul04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 803011521#u32 905020638#u32 1745802776#u32 762859377#u32) (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32)=ok (q 1219302266#u32 1404868535#u32 668157068#u32 736490375#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (803011521 < 2147483647 ∧ 905020638 < 2147483647) ∧ (1745802776 < 2147483647 ∧ 762859377 < 2147483647); omega) (by change (763754670 < 2147483647 ∧ 31463458 < 2147483647) ∧ (1727849165 < 2147483647 ∧ 1028580563 < 2147483647); omega) (by rfl)
#print axioms mul04
theorem add04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1219302266#u32 1404868535#u32 668157068#u32 736490375#u32) c04=ok (q 323839792#u32 247813096#u32 453200597#u32 1231568791#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1219302266 < 2147483647 ∧ 1404868535 < 2147483647) ∧ (668157068 < 2147483647 ∧ 736490375 < 2147483647); omega) canonical04 (by rfl)
#print axioms add04
theorem mul03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 323839792#u32 247813096#u32 453200597#u32 1231568791#u32) (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32)=ok (q 1733498850#u32 1792553998#u32 1740085645#u32 623393119#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (323839792 < 2147483647 ∧ 247813096 < 2147483647) ∧ (453200597 < 2147483647 ∧ 1231568791 < 2147483647); omega) (by change (763754670 < 2147483647 ∧ 31463458 < 2147483647) ∧ (1727849165 < 2147483647 ∧ 1028580563 < 2147483647); omega) (by rfl)
#print axioms mul03
theorem add03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1733498850#u32 1792553998#u32 1740085645#u32 623393119#u32) c03=ok (q 1938764399#u32 1411173511#u32 801992763#u32 397275399#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1733498850 < 2147483647 ∧ 1792553998 < 2147483647) ∧ (1740085645 < 2147483647 ∧ 623393119 < 2147483647); omega) canonical03 (by rfl)
#print axioms add03
theorem mul02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1938764399#u32 1411173511#u32 801992763#u32 397275399#u32) (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32)=ok (q 1319977115#u32 1816737810#u32 1911988560#u32 456540588#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1938764399 < 2147483647 ∧ 1411173511 < 2147483647) ∧ (801992763 < 2147483647 ∧ 397275399 < 2147483647); omega) (by change (763754670 < 2147483647 ∧ 31463458 < 2147483647) ∧ (1727849165 < 2147483647 ∧ 1028580563 < 2147483647); omega) (by rfl)
#print axioms mul02
theorem add02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1319977115#u32 1816737810#u32 1911988560#u32 456540588#u32) c02=ok (q 782355455#u32 1861164287#u32 1930088273#u32 840983572#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1319977115 < 2147483647 ∧ 1816737810 < 2147483647) ∧ (1911988560 < 2147483647 ∧ 456540588 < 2147483647); omega) canonical02 (by rfl)
#print axioms add02
theorem mul01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 782355455#u32 1861164287#u32 1930088273#u32 840983572#u32) (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32)=ok (q 14706295#u32 1363806690#u32 1991744513#u32 17368008#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (782355455 < 2147483647 ∧ 1861164287 < 2147483647) ∧ (1930088273 < 2147483647 ∧ 840983572 < 2147483647); omega) (by change (763754670 < 2147483647 ∧ 31463458 < 2147483647) ∧ (1727849165 < 2147483647 ∧ 1028580563 < 2147483647); omega) (by rfl)
#print axioms mul01
theorem add01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 14706295#u32 1363806690#u32 1991744513#u32 17368008#u32) c01=ok (q 374168570#u32 1279917198#u32 802331706#u32 710045871#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (14706295 < 2147483647 ∧ 1363806690 < 2147483647) ∧ (1991744513 < 2147483647 ∧ 17368008 < 2147483647); omega) canonical01 (by rfl)
#print axioms add01
theorem mul00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 374168570#u32 1279917198#u32 802331706#u32 710045871#u32) (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32)=ok (q 2147415786#u32 1011842819#u32 2128053033#u32 1143099559#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (374168570 < 2147483647 ∧ 1279917198 < 2147483647) ∧ (802331706 < 2147483647 ∧ 710045871 < 2147483647); omega) (by change (763754670 < 2147483647 ∧ 31463458 < 2147483647) ∧ (1727849165 < 2147483647 ∧ 1028580563 < 2147483647); omega) (by rfl)
#print axioms mul00
theorem add00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2147415786#u32 1011842819#u32 2128053033#u32 1143099559#u32) c00=ok (q 140564882#u32 1510799007#u32 831892455#u32 548159668#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2147415786 < 2147483647 ∧ 1011842819 < 2147483647) ∧ (2128053033 < 2147483647 ∧ 1143099559 < 2147483647); omega) canonical00 (by rfl)
#print axioms add00
def final : Q := (q 140564882#u32 1510799007#u32 831892455#u32 548159668#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 4#usize 14#usize initial 0#usize final := by
  refine .step (by change 14>0; omega) (JFr_IndexArithmetic.sub 14#usize 13#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32) from rfl) mul13 (show Array.index_usize p 13#usize=ok c13 from rfl) add13 ?_
  refine .step (by change 13>0; omega) (JFr_IndexArithmetic.sub 13#usize 12#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32) from rfl) mul12 (show Array.index_usize p 12#usize=ok c12 from rfl) add12 ?_
  refine .step (by change 12>0; omega) (JFr_IndexArithmetic.sub 12#usize 11#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32) from rfl) mul11 (show Array.index_usize p 11#usize=ok c11 from rfl) add11 ?_
  refine .step (by change 11>0; omega) (JFr_IndexArithmetic.sub 11#usize 10#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32) from rfl) mul10 (show Array.index_usize p 10#usize=ok c10 from rfl) add10 ?_
  refine .step (by change 10>0; omega) (JFr_IndexArithmetic.sub 10#usize 9#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32) from rfl) mul09 (show Array.index_usize p 9#usize=ok c09 from rfl) add09 ?_
  refine .step (by change 9>0; omega) (JFr_IndexArithmetic.sub 9#usize 8#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32) from rfl) mul08 (show Array.index_usize p 8#usize=ok c08 from rfl) add08 ?_
  refine .step (by change 8>0; omega) (JFr_IndexArithmetic.sub 8#usize 7#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32) from rfl) mul07 (show Array.index_usize p 7#usize=ok c07 from rfl) add07 ?_
  refine .step (by change 7>0; omega) (JFr_IndexArithmetic.sub 7#usize 6#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32) from rfl) mul06 (show Array.index_usize p 6#usize=ok c06 from rfl) add06 ?_
  refine .step (by change 6>0; omega) (JFr_IndexArithmetic.sub 6#usize 5#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32) from rfl) mul05 (show Array.index_usize p 5#usize=ok c05 from rfl) add05 ?_
  refine .step (by change 5>0; omega) (JFr_IndexArithmetic.sub 5#usize 4#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32) from rfl) mul04 (show Array.index_usize p 4#usize=ok c04 from rfl) add04 ?_
  refine .step (by change 4>0; omega) (JFr_IndexArithmetic.sub 4#usize 3#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32) from rfl) mul03 (show Array.index_usize p 3#usize=ok c03 from rfl) add03 ?_
  refine .step (by change 3>0; omega) (JFr_IndexArithmetic.sub 3#usize 2#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32) from rfl) mul02 (show Array.index_usize p 2#usize=ok c02 from rfl) add02 ?_
  refine .step (by change 2>0; omega) (JFr_IndexArithmetic.sub 2#usize 1#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32) from rfl) mul01 (show Array.index_usize p 1#usize=ok c01 from rfl) add01 ?_
  refine .step (by change 1>0; omega) (JFr_IndexArithmetic.sub 1#usize 0#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 763754670#u32 31463458#u32 1727849165#u32 1028580563#u32) from rfl) mul00 (show Array.index_usize p 0#usize=ok c00 from rfl) add00 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner04_1
