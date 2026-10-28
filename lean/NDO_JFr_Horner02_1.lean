import NDO_JFr_Data02
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner02_1
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data02
def initial : Q := (q 1162182785#u32 1928795309#u32 804238543#u32 295474589#u32)
theorem mul13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1162182785#u32 1928795309#u32 804238543#u32 295474589#u32) (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32)=ok (q 1044554433#u32 1525269041#u32 1408010471#u32 809556043#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1162182785 < 2147483647 ∧ 1928795309 < 2147483647) ∧ (804238543 < 2147483647 ∧ 295474589 < 2147483647); omega) (by change (1657509587 < 2147483647 ∧ 287924440 < 2147483647) ∧ (1819227394 < 2147483647 ∧ 1192254731 < 2147483647); omega) (by rfl)
#print axioms mul13
theorem add13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1044554433#u32 1525269041#u32 1408010471#u32 809556043#u32) c13=ok (q 185415253#u32 1185278490#u32 1202617772#u32 699777918#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1044554433 < 2147483647 ∧ 1525269041 < 2147483647) ∧ (1408010471 < 2147483647 ∧ 809556043 < 2147483647); omega) canonical13 (by rfl)
#print axioms add13
theorem mul12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 185415253#u32 1185278490#u32 1202617772#u32 699777918#u32) (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32)=ok (q 89431589#u32 731872960#u32 1950767769#u32 597549368#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (185415253 < 2147483647 ∧ 1185278490 < 2147483647) ∧ (1202617772 < 2147483647 ∧ 699777918 < 2147483647); omega) (by change (1657509587 < 2147483647 ∧ 287924440 < 2147483647) ∧ (1819227394 < 2147483647 ∧ 1192254731 < 2147483647); omega) (by rfl)
#print axioms mul12
theorem add12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 89431589#u32 731872960#u32 1950767769#u32 597549368#u32) c12=ok (q 771739590#u32 766288359#u32 1003366080#u32 1247252865#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (89431589 < 2147483647 ∧ 731872960 < 2147483647) ∧ (1950767769 < 2147483647 ∧ 597549368 < 2147483647); omega) canonical12 (by rfl)
#print axioms add12
theorem mul11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 771739590#u32 766288359#u32 1003366080#u32 1247252865#u32) (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32)=ok (q 1777149802#u32 25508821#u32 650218009#u32 577979861#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (771739590 < 2147483647 ∧ 766288359 < 2147483647) ∧ (1003366080 < 2147483647 ∧ 1247252865 < 2147483647); omega) (by change (1657509587 < 2147483647 ∧ 287924440 < 2147483647) ∧ (1819227394 < 2147483647 ∧ 1192254731 < 2147483647); omega) (by rfl)
#print axioms mul11
theorem add11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1777149802#u32 25508821#u32 650218009#u32 577979861#u32) c11=ok (q 1181284913#u32 171205531#u32 1261229547#u32 710450579#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1777149802 < 2147483647 ∧ 25508821 < 2147483647) ∧ (650218009 < 2147483647 ∧ 577979861 < 2147483647); omega) canonical11 (by rfl)
#print axioms add11
theorem mul10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1181284913#u32 171205531#u32 1261229547#u32 710450579#u32) (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32)=ok (q 428149739#u32 645247575#u32 139412372#u32 1741802820#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1181284913 < 2147483647 ∧ 171205531 < 2147483647) ∧ (1261229547 < 2147483647 ∧ 710450579 < 2147483647); omega) (by change (1657509587 < 2147483647 ∧ 287924440 < 2147483647) ∧ (1819227394 < 2147483647 ∧ 1192254731 < 2147483647); omega) (by rfl)
#print axioms mul10
theorem add10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 428149739#u32 645247575#u32 139412372#u32 1741802820#u32) c10=ok (q 1409922298#u32 505926908#u32 196320459#u32 1435340832#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (428149739 < 2147483647 ∧ 645247575 < 2147483647) ∧ (139412372 < 2147483647 ∧ 1741802820 < 2147483647); omega) canonical10 (by rfl)
#print axioms add10
theorem mul09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1409922298#u32 505926908#u32 196320459#u32 1435340832#u32) (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32)=ok (q 366198632#u32 1497597137#u32 1247999947#u32 1251962026#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1409922298 < 2147483647 ∧ 505926908 < 2147483647) ∧ (196320459 < 2147483647 ∧ 1435340832 < 2147483647); omega) (by change (1657509587 < 2147483647 ∧ 287924440 < 2147483647) ∧ (1819227394 < 2147483647 ∧ 1192254731 < 2147483647); omega) (by rfl)
#print axioms mul09
theorem add09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 366198632#u32 1497597137#u32 1247999947#u32 1251962026#u32) c09=ok (q 2102632599#u32 1332974685#u32 2094724659#u32 1800518554#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (366198632 < 2147483647 ∧ 1497597137 < 2147483647) ∧ (1247999947 < 2147483647 ∧ 1251962026 < 2147483647); omega) canonical09 (by rfl)
#print axioms add09
theorem mul08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2102632599#u32 1332974685#u32 2094724659#u32 1800518554#u32) (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32)=ok (q 1520980820#u32 1740909496#u32 888011594#u32 225152547#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2102632599 < 2147483647 ∧ 1332974685 < 2147483647) ∧ (2094724659 < 2147483647 ∧ 1800518554 < 2147483647); omega) (by change (1657509587 < 2147483647 ∧ 287924440 < 2147483647) ∧ (1819227394 < 2147483647 ∧ 1192254731 < 2147483647); omega) (by rfl)
#print axioms mul08
theorem add08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1520980820#u32 1740909496#u32 888011594#u32 225152547#u32) c08=ok (q 1195939041#u32 741196639#u32 1652456053#u32 252389814#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1520980820 < 2147483647 ∧ 1740909496 < 2147483647) ∧ (888011594 < 2147483647 ∧ 225152547 < 2147483647); omega) canonical08 (by rfl)
#print axioms add08
theorem mul07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1195939041#u32 741196639#u32 1652456053#u32 252389814#u32) (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32)=ok (q 528190287#u32 1879581057#u32 1904225107#u32 1063978776#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1195939041 < 2147483647 ∧ 741196639 < 2147483647) ∧ (1652456053 < 2147483647 ∧ 252389814 < 2147483647); omega) (by change (1657509587 < 2147483647 ∧ 287924440 < 2147483647) ∧ (1819227394 < 2147483647 ∧ 1192254731 < 2147483647); omega) (by rfl)
#print axioms mul07
theorem add07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 528190287#u32 1879581057#u32 1904225107#u32 1063978776#u32) c07=ok (q 1720117950#u32 3529522#u32 1486242928#u32 468977001#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (528190287 < 2147483647 ∧ 1879581057 < 2147483647) ∧ (1904225107 < 2147483647 ∧ 1063978776 < 2147483647); omega) canonical07 (by rfl)
#print axioms add07
theorem mul06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1720117950#u32 3529522#u32 1486242928#u32 468977001#u32) (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32)=ok (q 1475892591#u32 26253902#u32 1700540972#u32 1827560003#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1720117950 < 2147483647 ∧ 3529522 < 2147483647) ∧ (1486242928 < 2147483647 ∧ 468977001 < 2147483647); omega) (by change (1657509587 < 2147483647 ∧ 287924440 < 2147483647) ∧ (1819227394 < 2147483647 ∧ 1192254731 < 2147483647); omega) (by rfl)
#print axioms mul06
theorem add06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1475892591#u32 26253902#u32 1700540972#u32 1827560003#u32) c06=ok (q 1518493021#u32 1198520190#u32 1996515756#u32 555749312#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1475892591 < 2147483647 ∧ 26253902 < 2147483647) ∧ (1700540972 < 2147483647 ∧ 1827560003 < 2147483647); omega) canonical06 (by rfl)
#print axioms add06
theorem mul05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1518493021#u32 1198520190#u32 1996515756#u32 555749312#u32) (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32)=ok (q 1077638582#u32 1547924738#u32 1970286218#u32 701178592#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1518493021 < 2147483647 ∧ 1198520190 < 2147483647) ∧ (1996515756 < 2147483647 ∧ 555749312 < 2147483647); omega) (by change (1657509587 < 2147483647 ∧ 287924440 < 2147483647) ∧ (1819227394 < 2147483647 ∧ 1192254731 < 2147483647); omega) (by rfl)
#print axioms mul05
theorem add05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1077638582#u32 1547924738#u32 1970286218#u32 701178592#u32) c05=ok (q 477192215#u32 1731463035#u32 1901681858#u32 212166485#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1077638582 < 2147483647 ∧ 1547924738 < 2147483647) ∧ (1970286218 < 2147483647 ∧ 701178592 < 2147483647); omega) canonical05 (by rfl)
#print axioms add05
theorem mul04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 477192215#u32 1731463035#u32 1901681858#u32 212166485#u32) (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32)=ok (q 2096804916#u32 1785148253#u32 278825371#u32 909531149#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (477192215 < 2147483647 ∧ 1731463035 < 2147483647) ∧ (1901681858 < 2147483647 ∧ 212166485 < 2147483647); omega) (by change (1657509587 < 2147483647 ∧ 287924440 < 2147483647) ∧ (1819227394 < 2147483647 ∧ 1192254731 < 2147483647); omega) (by rfl)
#print axioms mul04
theorem add04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2096804916#u32 1785148253#u32 278825371#u32 909531149#u32) c04=ok (q 1872478209#u32 970067959#u32 970473452#u32 571593011#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2096804916 < 2147483647 ∧ 1785148253 < 2147483647) ∧ (278825371 < 2147483647 ∧ 909531149 < 2147483647); omega) canonical04 (by rfl)
#print axioms add04
theorem mul03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1872478209#u32 970067959#u32 970473452#u32 571593011#u32) (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32)=ok (q 809428920#u32 1552184087#u32 2111326160#u32 125501672#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1872478209 < 2147483647 ∧ 970067959 < 2147483647) ∧ (970473452 < 2147483647 ∧ 571593011 < 2147483647); omega) (by change (1657509587 < 2147483647 ∧ 287924440 < 2147483647) ∧ (1819227394 < 2147483647 ∧ 1192254731 < 2147483647); omega) (by rfl)
#print axioms mul03
theorem add03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 809428920#u32 1552184087#u32 2111326160#u32 125501672#u32) c03=ok (q 276083796#u32 2116284295#u32 2041424712#u32 799288815#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (809428920 < 2147483647 ∧ 1552184087 < 2147483647) ∧ (2111326160 < 2147483647 ∧ 125501672 < 2147483647); omega) canonical03 (by rfl)
#print axioms add03
theorem mul02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 276083796#u32 2116284295#u32 2041424712#u32 799288815#u32) (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32)=ok (q 1391460984#u32 774373144#u32 397177312#u32 1951342746#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (276083796 < 2147483647 ∧ 2116284295 < 2147483647) ∧ (2041424712 < 2147483647 ∧ 799288815 < 2147483647); omega) (by change (1657509587 < 2147483647 ∧ 287924440 < 2147483647) ∧ (1819227394 < 2147483647 ∧ 1192254731 < 2147483647); omega) (by rfl)
#print axioms mul02
theorem add02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1391460984#u32 774373144#u32 397177312#u32 1951342746#u32) c02=ok (q 108416600#u32 166488244#u32 963170357#u32 103372975#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1391460984 < 2147483647 ∧ 774373144 < 2147483647) ∧ (397177312 < 2147483647 ∧ 1951342746 < 2147483647); omega) canonical02 (by rfl)
#print axioms add02
theorem mul01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 108416600#u32 166488244#u32 963170357#u32 103372975#u32) (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32)=ok (q 562974806#u32 220787043#u32 546063132#u32 1038095345#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (108416600 < 2147483647 ∧ 166488244 < 2147483647) ∧ (963170357 < 2147483647 ∧ 103372975 < 2147483647); omega) (by change (1657509587 < 2147483647 ∧ 287924440 < 2147483647) ∧ (1819227394 < 2147483647 ∧ 1192254731 < 2147483647); omega) (by rfl)
#print axioms mul01
theorem add01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 562974806#u32 220787043#u32 546063132#u32 1038095345#u32) c01=ok (q 1855246767#u32 1072550191#u32 969771900#u32 1319467413#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (562974806 < 2147483647 ∧ 220787043 < 2147483647) ∧ (546063132 < 2147483647 ∧ 1038095345 < 2147483647); omega) canonical01 (by rfl)
#print axioms add01
theorem mul00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1855246767#u32 1072550191#u32 969771900#u32 1319467413#u32) (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32)=ok (q 1582501422#u32 290020564#u32 1744072090#u32 393039388#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1855246767 < 2147483647 ∧ 1072550191 < 2147483647) ∧ (969771900 < 2147483647 ∧ 1319467413 < 2147483647); omega) (by change (1657509587 < 2147483647 ∧ 287924440 < 2147483647) ∧ (1819227394 < 2147483647 ∧ 1192254731 < 2147483647); omega) (by rfl)
#print axioms mul00
theorem add00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1582501422#u32 290020564#u32 1744072090#u32 393039388#u32) c00=ok (q 1369839722#u32 591220065#u32 881134391#u32 1429243240#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1582501422 < 2147483647 ∧ 290020564 < 2147483647) ∧ (1744072090 < 2147483647 ∧ 393039388 < 2147483647); omega) canonical00 (by rfl)
#print axioms add00
def final : Q := (q 1369839722#u32 591220065#u32 881134391#u32 1429243240#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 2#usize 14#usize initial 0#usize final := by
  refine .step (by change 14>0; omega) (JFr_IndexArithmetic.sub 14#usize 13#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32) from rfl) mul13 (show Array.index_usize p 13#usize=ok c13 from rfl) add13 ?_
  refine .step (by change 13>0; omega) (JFr_IndexArithmetic.sub 13#usize 12#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32) from rfl) mul12 (show Array.index_usize p 12#usize=ok c12 from rfl) add12 ?_
  refine .step (by change 12>0; omega) (JFr_IndexArithmetic.sub 12#usize 11#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32) from rfl) mul11 (show Array.index_usize p 11#usize=ok c11 from rfl) add11 ?_
  refine .step (by change 11>0; omega) (JFr_IndexArithmetic.sub 11#usize 10#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32) from rfl) mul10 (show Array.index_usize p 10#usize=ok c10 from rfl) add10 ?_
  refine .step (by change 10>0; omega) (JFr_IndexArithmetic.sub 10#usize 9#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32) from rfl) mul09 (show Array.index_usize p 9#usize=ok c09 from rfl) add09 ?_
  refine .step (by change 9>0; omega) (JFr_IndexArithmetic.sub 9#usize 8#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32) from rfl) mul08 (show Array.index_usize p 8#usize=ok c08 from rfl) add08 ?_
  refine .step (by change 8>0; omega) (JFr_IndexArithmetic.sub 8#usize 7#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32) from rfl) mul07 (show Array.index_usize p 7#usize=ok c07 from rfl) add07 ?_
  refine .step (by change 7>0; omega) (JFr_IndexArithmetic.sub 7#usize 6#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32) from rfl) mul06 (show Array.index_usize p 6#usize=ok c06 from rfl) add06 ?_
  refine .step (by change 6>0; omega) (JFr_IndexArithmetic.sub 6#usize 5#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32) from rfl) mul05 (show Array.index_usize p 5#usize=ok c05 from rfl) add05 ?_
  refine .step (by change 5>0; omega) (JFr_IndexArithmetic.sub 5#usize 4#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32) from rfl) mul04 (show Array.index_usize p 4#usize=ok c04 from rfl) add04 ?_
  refine .step (by change 4>0; omega) (JFr_IndexArithmetic.sub 4#usize 3#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32) from rfl) mul03 (show Array.index_usize p 3#usize=ok c03 from rfl) add03 ?_
  refine .step (by change 3>0; omega) (JFr_IndexArithmetic.sub 3#usize 2#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32) from rfl) mul02 (show Array.index_usize p 2#usize=ok c02 from rfl) add02 ?_
  refine .step (by change 2>0; omega) (JFr_IndexArithmetic.sub 2#usize 1#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32) from rfl) mul01 (show Array.index_usize p 1#usize=ok c01 from rfl) add01 ?_
  refine .step (by change 1>0; omega) (JFr_IndexArithmetic.sub 1#usize 0#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32) from rfl) mul00 (show Array.index_usize p 0#usize=ok c00 from rfl) add00 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner02_1
