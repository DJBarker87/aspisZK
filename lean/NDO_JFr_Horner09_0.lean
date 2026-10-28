import NDO_JFr_Data09
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner09_0
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data09
def initial : Q := (q 0#u32 0#u32 0#u32 0#u32)
theorem mul27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 0#u32 0#u32 0#u32 0#u32) (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32)=ok (q 0#u32 0#u32 0#u32 0#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) (by change (2030227143 < 2147483647 ∧ 1410410828 < 2147483647) ∧ (1902035786 < 2147483647 ∧ 62756635 < 2147483647); omega) (by rfl)
#print axioms mul27
theorem add27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 0#u32 0#u32 0#u32 0#u32) c27=ok (q 1481893523#u32 1948286100#u32 1829200971#u32 680578994#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) canonical27 (by rfl)
#print axioms add27
theorem mul26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1481893523#u32 1948286100#u32 1829200971#u32 680578994#u32) (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32)=ok (q 1449341469#u32 570492678#u32 1995173818#u32 515502234#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1481893523 < 2147483647 ∧ 1948286100 < 2147483647) ∧ (1829200971 < 2147483647 ∧ 680578994 < 2147483647); omega) (by change (2030227143 < 2147483647 ∧ 1410410828 < 2147483647) ∧ (1902035786 < 2147483647 ∧ 62756635 < 2147483647); omega) (by rfl)
#print axioms mul26
theorem add26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1449341469#u32 570492678#u32 1995173818#u32 515502234#u32) c26=ok (q 540972906#u32 2111745580#u32 1037719344#u32 593423992#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1449341469 < 2147483647 ∧ 570492678 < 2147483647) ∧ (1995173818 < 2147483647 ∧ 515502234 < 2147483647); omega) canonical26 (by rfl)
#print axioms add26
theorem mul25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 540972906#u32 2111745580#u32 1037719344#u32 593423992#u32) (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32)=ok (q 1599017065#u32 1990347628#u32 531612488#u32 1265824773#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (540972906 < 2147483647 ∧ 2111745580 < 2147483647) ∧ (1037719344 < 2147483647 ∧ 593423992 < 2147483647); omega) (by change (2030227143 < 2147483647 ∧ 1410410828 < 2147483647) ∧ (1902035786 < 2147483647 ∧ 62756635 < 2147483647); omega) (by rfl)
#print axioms mul25
theorem add25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1599017065#u32 1990347628#u32 531612488#u32 1265824773#u32) c25=ok (q 331901914#u32 1522547362#u32 868985560#u32 1401065390#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1599017065 < 2147483647 ∧ 1990347628 < 2147483647) ∧ (531612488 < 2147483647 ∧ 1265824773 < 2147483647); omega) canonical25 (by rfl)
#print axioms add25
theorem mul24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 331901914#u32 1522547362#u32 868985560#u32 1401065390#u32) (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32)=ok (q 1014133905#u32 591162730#u32 1490159666#u32 2113474830#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (331901914 < 2147483647 ∧ 1522547362 < 2147483647) ∧ (868985560 < 2147483647 ∧ 1401065390 < 2147483647); omega) (by change (2030227143 < 2147483647 ∧ 1410410828 < 2147483647) ∧ (1902035786 < 2147483647 ∧ 62756635 < 2147483647); omega) (by rfl)
#print axioms mul24
theorem add24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1014133905#u32 591162730#u32 1490159666#u32 2113474830#u32) c24=ok (q 1297339136#u32 212580677#u32 222727883#u32 2085574586#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1014133905 < 2147483647 ∧ 591162730 < 2147483647) ∧ (1490159666 < 2147483647 ∧ 2113474830 < 2147483647); omega) canonical24 (by rfl)
#print axioms add24
theorem mul23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1297339136#u32 212580677#u32 222727883#u32 2085574586#u32) (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32)=ok (q 1765043824#u32 1696445495#u32 654769042#u32 1227058726#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1297339136 < 2147483647 ∧ 212580677 < 2147483647) ∧ (222727883 < 2147483647 ∧ 2085574586 < 2147483647); omega) (by change (2030227143 < 2147483647 ∧ 1410410828 < 2147483647) ∧ (1902035786 < 2147483647 ∧ 62756635 < 2147483647); omega) (by rfl)
#print axioms mul23
theorem add23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1765043824#u32 1696445495#u32 654769042#u32 1227058726#u32) c23=ok (q 64292200#u32 2018479793#u32 2105490142#u32 1338018422#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1765043824 < 2147483647 ∧ 1696445495 < 2147483647) ∧ (654769042 < 2147483647 ∧ 1227058726 < 2147483647); omega) canonical23 (by rfl)
#print axioms add23
theorem mul22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 64292200#u32 2018479793#u32 2105490142#u32 1338018422#u32) (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32)=ok (q 1208966014#u32 851847526#u32 1637910617#u32 1586472874#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (64292200 < 2147483647 ∧ 2018479793 < 2147483647) ∧ (2105490142 < 2147483647 ∧ 1338018422 < 2147483647); omega) (by change (2030227143 < 2147483647 ∧ 1410410828 < 2147483647) ∧ (1902035786 < 2147483647 ∧ 62756635 < 2147483647); omega) (by rfl)
#print axioms mul22
theorem add22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1208966014#u32 851847526#u32 1637910617#u32 1586472874#u32) c22=ok (q 1454838411#u32 1355064398#u32 1172291310#u32 49656568#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1208966014 < 2147483647 ∧ 851847526 < 2147483647) ∧ (1637910617 < 2147483647 ∧ 1586472874 < 2147483647); omega) canonical22 (by rfl)
#print axioms add22
theorem mul21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1454838411#u32 1355064398#u32 1172291310#u32 49656568#u32) (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32)=ok (q 1809315218#u32 2001083395#u32 1522595770#u32 1292106960#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1454838411 < 2147483647 ∧ 1355064398 < 2147483647) ∧ (1172291310 < 2147483647 ∧ 49656568 < 2147483647); omega) (by change (2030227143 < 2147483647 ∧ 1410410828 < 2147483647) ∧ (1902035786 < 2147483647 ∧ 62756635 < 2147483647); omega) (by rfl)
#print axioms mul21
theorem add21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1809315218#u32 2001083395#u32 1522595770#u32 1292106960#u32) c21=ok (q 745437737#u32 1347438956#u32 1797557402#u32 1250176835#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1809315218 < 2147483647 ∧ 2001083395 < 2147483647) ∧ (1522595770 < 2147483647 ∧ 1292106960 < 2147483647); omega) canonical21 (by rfl)
#print axioms add21
theorem mul20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 745437737#u32 1347438956#u32 1797557402#u32 1250176835#u32) (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32)=ok (q 1574709363#u32 319228678#u32 727862508#u32 921389802#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (745437737 < 2147483647 ∧ 1347438956 < 2147483647) ∧ (1797557402 < 2147483647 ∧ 1250176835 < 2147483647); omega) (by change (2030227143 < 2147483647 ∧ 1410410828 < 2147483647) ∧ (1902035786 < 2147483647 ∧ 62756635 < 2147483647); omega) (by rfl)
#print axioms mul20
theorem add20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1574709363#u32 319228678#u32 727862508#u32 921389802#u32) c20=ok (q 334568791#u32 275917934#u32 325848353#u32 378135463#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1574709363 < 2147483647 ∧ 319228678 < 2147483647) ∧ (727862508 < 2147483647 ∧ 921389802 < 2147483647); omega) canonical20 (by rfl)
#print axioms add20
theorem mul19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 334568791#u32 275917934#u32 325848353#u32 378135463#u32) (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32)=ok (q 694472144#u32 1561697963#u32 295321976#u32 1064834559#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (334568791 < 2147483647 ∧ 275917934 < 2147483647) ∧ (325848353 < 2147483647 ∧ 378135463 < 2147483647); omega) (by change (2030227143 < 2147483647 ∧ 1410410828 < 2147483647) ∧ (1902035786 < 2147483647 ∧ 62756635 < 2147483647); omega) (by rfl)
#print axioms mul19
theorem add19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 694472144#u32 1561697963#u32 295321976#u32 1064834559#u32) c19=ok (q 1334974046#u32 266305895#u32 562658385#u32 1985752986#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (694472144 < 2147483647 ∧ 1561697963 < 2147483647) ∧ (295321976 < 2147483647 ∧ 1064834559 < 2147483647); omega) canonical19 (by rfl)
#print axioms add19
theorem mul18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1334974046#u32 266305895#u32 562658385#u32 1985752986#u32) (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32)=ok (q 1881362444#u32 1893306376#u32 824518238#u32 1016285059#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1334974046 < 2147483647 ∧ 266305895 < 2147483647) ∧ (562658385 < 2147483647 ∧ 1985752986 < 2147483647); omega) (by change (2030227143 < 2147483647 ∧ 1410410828 < 2147483647) ∧ (1902035786 < 2147483647 ∧ 62756635 < 2147483647); omega) (by rfl)
#print axioms mul18
theorem add18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1881362444#u32 1893306376#u32 824518238#u32 1016285059#u32) c18=ok (q 1718316984#u32 1391621281#u32 1986759920#u32 624197573#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1881362444 < 2147483647 ∧ 1893306376 < 2147483647) ∧ (824518238 < 2147483647 ∧ 1016285059 < 2147483647); omega) canonical18 (by rfl)
#print axioms add18
theorem mul17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1718316984#u32 1391621281#u32 1986759920#u32 624197573#u32) (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32)=ok (q 1862084527#u32 1646115134#u32 755914447#u32 1579113408#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1718316984 < 2147483647 ∧ 1391621281 < 2147483647) ∧ (1986759920 < 2147483647 ∧ 624197573 < 2147483647); omega) (by change (2030227143 < 2147483647 ∧ 1410410828 < 2147483647) ∧ (1902035786 < 2147483647 ∧ 62756635 < 2147483647); omega) (by rfl)
#print axioms mul17
theorem add17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1862084527#u32 1646115134#u32 755914447#u32 1579113408#u32) c17=ok (q 1396209961#u32 504747348#u32 801766256#u32 1555407921#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1862084527 < 2147483647 ∧ 1646115134 < 2147483647) ∧ (755914447 < 2147483647 ∧ 1579113408 < 2147483647); omega) canonical17 (by rfl)
#print axioms add17
theorem mul16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1396209961#u32 504747348#u32 801766256#u32 1555407921#u32) (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32)=ok (q 1090135224#u32 1384193662#u32 1449193578#u32 2111051711#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1396209961 < 2147483647 ∧ 504747348 < 2147483647) ∧ (801766256 < 2147483647 ∧ 1555407921 < 2147483647); omega) (by change (2030227143 < 2147483647 ∧ 1410410828 < 2147483647) ∧ (1902035786 < 2147483647 ∧ 62756635 < 2147483647); omega) (by rfl)
#print axioms mul16
theorem add16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1090135224#u32 1384193662#u32 1449193578#u32 2111051711#u32) c16=ok (q 1070755870#u32 522885833#u32 878409881#u32 1741272475#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1090135224 < 2147483647 ∧ 1384193662 < 2147483647) ∧ (1449193578 < 2147483647 ∧ 2111051711 < 2147483647); omega) canonical16 (by rfl)
#print axioms add16
theorem mul15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1070755870#u32 522885833#u32 878409881#u32 1741272475#u32) (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32)=ok (q 1700592091#u32 1099491655#u32 1192735363#u32 910145800#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1070755870 < 2147483647 ∧ 522885833 < 2147483647) ∧ (878409881 < 2147483647 ∧ 1741272475 < 2147483647); omega) (by change (2030227143 < 2147483647 ∧ 1410410828 < 2147483647) ∧ (1902035786 < 2147483647 ∧ 62756635 < 2147483647); omega) (by rfl)
#print axioms mul15
theorem add15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1700592091#u32 1099491655#u32 1192735363#u32 910145800#u32) c15=ok (q 1923009080#u32 862284942#u32 1494561619#u32 425303019#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1700592091 < 2147483647 ∧ 1099491655 < 2147483647) ∧ (1192735363 < 2147483647 ∧ 910145800 < 2147483647); omega) canonical15 (by rfl)
#print axioms add15
theorem mul14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1923009080#u32 862284942#u32 1494561619#u32 425303019#u32) (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32)=ok (q 291355551#u32 1844889367#u32 1103428955#u32 1960308863#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1923009080 < 2147483647 ∧ 862284942 < 2147483647) ∧ (1494561619 < 2147483647 ∧ 425303019 < 2147483647); omega) (by change (2030227143 < 2147483647 ∧ 1410410828 < 2147483647) ∧ (1902035786 < 2147483647 ∧ 62756635 < 2147483647); omega) (by rfl)
#print axioms mul14
theorem add14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 291355551#u32 1844889367#u32 1103428955#u32 1960308863#u32) c14=ok (q 837512584#u32 1034806050#u32 1840833632#u32 1131458616#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (291355551 < 2147483647 ∧ 1844889367 < 2147483647) ∧ (1103428955 < 2147483647 ∧ 1960308863 < 2147483647); omega) canonical14 (by rfl)
#print axioms add14
def final : Q := (q 837512584#u32 1034806050#u32 1840833632#u32 1131458616#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 9#usize 28#usize initial 14#usize final := by
  refine .step (by change 28>0; omega) (JFr_IndexArithmetic.sub 28#usize 27#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32) from rfl) mul27 (show Array.index_usize p 27#usize=ok c27 from rfl) add27 ?_
  refine .step (by change 27>0; omega) (JFr_IndexArithmetic.sub 27#usize 26#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32) from rfl) mul26 (show Array.index_usize p 26#usize=ok c26 from rfl) add26 ?_
  refine .step (by change 26>0; omega) (JFr_IndexArithmetic.sub 26#usize 25#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32) from rfl) mul25 (show Array.index_usize p 25#usize=ok c25 from rfl) add25 ?_
  refine .step (by change 25>0; omega) (JFr_IndexArithmetic.sub 25#usize 24#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32) from rfl) mul24 (show Array.index_usize p 24#usize=ok c24 from rfl) add24 ?_
  refine .step (by change 24>0; omega) (JFr_IndexArithmetic.sub 24#usize 23#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32) from rfl) mul23 (show Array.index_usize p 23#usize=ok c23 from rfl) add23 ?_
  refine .step (by change 23>0; omega) (JFr_IndexArithmetic.sub 23#usize 22#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32) from rfl) mul22 (show Array.index_usize p 22#usize=ok c22 from rfl) add22 ?_
  refine .step (by change 22>0; omega) (JFr_IndexArithmetic.sub 22#usize 21#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32) from rfl) mul21 (show Array.index_usize p 21#usize=ok c21 from rfl) add21 ?_
  refine .step (by change 21>0; omega) (JFr_IndexArithmetic.sub 21#usize 20#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32) from rfl) mul20 (show Array.index_usize p 20#usize=ok c20 from rfl) add20 ?_
  refine .step (by change 20>0; omega) (JFr_IndexArithmetic.sub 20#usize 19#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32) from rfl) mul19 (show Array.index_usize p 19#usize=ok c19 from rfl) add19 ?_
  refine .step (by change 19>0; omega) (JFr_IndexArithmetic.sub 19#usize 18#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32) from rfl) mul18 (show Array.index_usize p 18#usize=ok c18 from rfl) add18 ?_
  refine .step (by change 18>0; omega) (JFr_IndexArithmetic.sub 18#usize 17#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32) from rfl) mul17 (show Array.index_usize p 17#usize=ok c17 from rfl) add17 ?_
  refine .step (by change 17>0; omega) (JFr_IndexArithmetic.sub 17#usize 16#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32) from rfl) mul16 (show Array.index_usize p 16#usize=ok c16 from rfl) add16 ?_
  refine .step (by change 16>0; omega) (JFr_IndexArithmetic.sub 16#usize 15#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32) from rfl) mul15 (show Array.index_usize p 15#usize=ok c15 from rfl) add15 ?_
  refine .step (by change 15>0; omega) (JFr_IndexArithmetic.sub 15#usize 14#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32) from rfl) mul14 (show Array.index_usize p 14#usize=ok c14 from rfl) add14 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner09_0
