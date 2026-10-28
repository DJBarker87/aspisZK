import NDO_JFr_Data07
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner07_0
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data07
def initial : Q := (q 0#u32 0#u32 0#u32 0#u32)
theorem mul27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 0#u32 0#u32 0#u32 0#u32) (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32)=ok (q 0#u32 0#u32 0#u32 0#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) (by change (2023864416 < 2147483647 ∧ 983081232 < 2147483647) ∧ (187881185 < 2147483647 ∧ 1338388013 < 2147483647); omega) (by rfl)
#print axioms mul27
theorem add27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 0#u32 0#u32 0#u32 0#u32) c27=ok (q 128581143#u32 793181979#u32 2061133312#u32 1841017006#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) canonical27 (by rfl)
#print axioms add27
theorem mul26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 128581143#u32 793181979#u32 2061133312#u32 1841017006#u32) (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32)=ok (q 1098993763#u32 728353802#u32 1541953189#u32 1634467206#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (128581143 < 2147483647 ∧ 793181979 < 2147483647) ∧ (2061133312 < 2147483647 ∧ 1841017006 < 2147483647); omega) (by change (2023864416 < 2147483647 ∧ 983081232 < 2147483647) ∧ (187881185 < 2147483647 ∧ 1338388013 < 2147483647); omega) (by rfl)
#print axioms mul26
theorem add26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1098993763#u32 728353802#u32 1541953189#u32 1634467206#u32) c26=ok (q 1148675727#u32 1915451748#u32 992192055#u32 1518960116#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1098993763 < 2147483647 ∧ 728353802 < 2147483647) ∧ (1541953189 < 2147483647 ∧ 1634467206 < 2147483647); omega) canonical26 (by rfl)
#print axioms add26
theorem mul25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1148675727#u32 1915451748#u32 992192055#u32 1518960116#u32) (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32)=ok (q 1753314058#u32 1090146064#u32 1101833497#u32 1749046588#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1148675727 < 2147483647 ∧ 1915451748 < 2147483647) ∧ (992192055 < 2147483647 ∧ 1518960116 < 2147483647); omega) (by change (2023864416 < 2147483647 ∧ 983081232 < 2147483647) ∧ (187881185 < 2147483647 ∧ 1338388013 < 2147483647); omega) (by rfl)
#print axioms mul25
theorem add25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1753314058#u32 1090146064#u32 1101833497#u32 1749046588#u32) c25=ok (q 1905706650#u32 2084999495#u32 1208211827#u32 938065355#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1753314058 < 2147483647 ∧ 1090146064 < 2147483647) ∧ (1101833497 < 2147483647 ∧ 1749046588 < 2147483647); omega) canonical25 (by rfl)
#print axioms add25
theorem mul24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1905706650#u32 2084999495#u32 1208211827#u32 938065355#u32) (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32)=ok (q 1323735220#u32 2142591563#u32 595707600#u32 251157105#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1905706650 < 2147483647 ∧ 2084999495 < 2147483647) ∧ (1208211827 < 2147483647 ∧ 938065355 < 2147483647); omega) (by change (2023864416 < 2147483647 ∧ 983081232 < 2147483647) ∧ (187881185 < 2147483647 ∧ 1338388013 < 2147483647); omega) (by rfl)
#print axioms mul24
theorem add24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1323735220#u32 2142591563#u32 595707600#u32 251157105#u32) c24=ok (q 1810523778#u32 650297234#u32 384644632#u32 370443096#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1323735220 < 2147483647 ∧ 2142591563 < 2147483647) ∧ (595707600 < 2147483647 ∧ 251157105 < 2147483647); omega) canonical24 (by rfl)
#print axioms add24
theorem mul23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1810523778#u32 650297234#u32 384644632#u32 370443096#u32) (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32)=ok (q 1601906934#u32 1402093199#u32 68705691#u32 2105187546#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1810523778 < 2147483647 ∧ 650297234 < 2147483647) ∧ (384644632 < 2147483647 ∧ 370443096 < 2147483647); omega) (by change (2023864416 < 2147483647 ∧ 983081232 < 2147483647) ∧ (187881185 < 2147483647 ∧ 1338388013 < 2147483647); omega) (by rfl)
#print axioms mul23
theorem add23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1601906934#u32 1402093199#u32 68705691#u32 2105187546#u32) c23=ok (q 555279396#u32 1276365575#u32 670659355#u32 814704773#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1601906934 < 2147483647 ∧ 1402093199 < 2147483647) ∧ (68705691 < 2147483647 ∧ 2105187546 < 2147483647); omega) canonical23 (by rfl)
#print axioms add23
theorem mul22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 555279396#u32 1276365575#u32 670659355#u32 814704773#u32) (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32)=ok (q 1333748496#u32 1846460208#u32 784519228#u32 1184487726#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (555279396 < 2147483647 ∧ 1276365575 < 2147483647) ∧ (670659355 < 2147483647 ∧ 814704773 < 2147483647); omega) (by change (2023864416 < 2147483647 ∧ 983081232 < 2147483647) ∧ (187881185 < 2147483647 ∧ 1338388013 < 2147483647); omega) (by rfl)
#print axioms mul22
theorem add22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1333748496#u32 1846460208#u32 784519228#u32 1184487726#u32) c22=ok (q 1847794716#u32 1481447381#u32 122732343#u32 2103441445#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1333748496 < 2147483647 ∧ 1846460208 < 2147483647) ∧ (784519228 < 2147483647 ∧ 1184487726 < 2147483647); omega) canonical22 (by rfl)
#print axioms add22
theorem mul21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1847794716#u32 1481447381#u32 122732343#u32 2103441445#u32) (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32)=ok (q 1734991454#u32 2036216183#u32 1453426658#u32 1352318185#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1847794716 < 2147483647 ∧ 1481447381 < 2147483647) ∧ (122732343 < 2147483647 ∧ 2103441445 < 2147483647); omega) (by change (2023864416 < 2147483647 ∧ 983081232 < 2147483647) ∧ (187881185 < 2147483647 ∧ 1338388013 < 2147483647); omega) (by rfl)
#print axioms mul21
theorem add21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1734991454#u32 2036216183#u32 1453426658#u32 1352318185#u32) c21=ok (q 1074350415#u32 1485147847#u32 1618385468#u32 241451076#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1734991454 < 2147483647 ∧ 2036216183 < 2147483647) ∧ (1453426658 < 2147483647 ∧ 1352318185 < 2147483647); omega) canonical21 (by rfl)
#print axioms add21
theorem mul20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1074350415#u32 1485147847#u32 1618385468#u32 241451076#u32) (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32)=ok (q 253606472#u32 1488270933#u32 110560493#u32 1434040315#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1074350415 < 2147483647 ∧ 1485147847 < 2147483647) ∧ (1618385468 < 2147483647 ∧ 241451076 < 2147483647); omega) (by change (2023864416 < 2147483647 ∧ 983081232 < 2147483647) ∧ (187881185 < 2147483647 ∧ 1338388013 < 2147483647); omega) (by rfl)
#print axioms mul20
theorem add20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 253606472#u32 1488270933#u32 110560493#u32 1434040315#u32) c20=ok (q 780620249#u32 265244280#u32 762058678#u32 612931825#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (253606472 < 2147483647 ∧ 1488270933 < 2147483647) ∧ (110560493 < 2147483647 ∧ 1434040315 < 2147483647); omega) canonical20 (by rfl)
#print axioms add20
theorem mul19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 780620249#u32 265244280#u32 762058678#u32 612931825#u32) (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32)=ok (q 1744214993#u32 373864692#u32 2145878564#u32 1872637780#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (780620249 < 2147483647 ∧ 265244280 < 2147483647) ∧ (762058678 < 2147483647 ∧ 612931825 < 2147483647); omega) (by change (2023864416 < 2147483647 ∧ 983081232 < 2147483647) ∧ (187881185 < 2147483647 ∧ 1338388013 < 2147483647); omega) (by rfl)
#print axioms mul19
theorem add19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1744214993#u32 373864692#u32 2145878564#u32 1872637780#u32) c19=ok (q 1495334106#u32 1811494341#u32 307505350#u32 1221634021#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1744214993 < 2147483647 ∧ 373864692 < 2147483647) ∧ (2145878564 < 2147483647 ∧ 1872637780 < 2147483647); omega) canonical19 (by rfl)
#print axioms add19
theorem mul18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1495334106#u32 1811494341#u32 307505350#u32 1221634021#u32) (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32)=ok (q 970822275#u32 1360556665#u32 861316228#u32 129397094#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1495334106 < 2147483647 ∧ 1811494341 < 2147483647) ∧ (307505350 < 2147483647 ∧ 1221634021 < 2147483647); omega) (by change (2023864416 < 2147483647 ∧ 983081232 < 2147483647) ∧ (187881185 < 2147483647 ∧ 1338388013 < 2147483647); omega) (by rfl)
#print axioms mul18
theorem add18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 970822275#u32 1360556665#u32 861316228#u32 129397094#u32) c18=ok (q 68461852#u32 300409289#u32 928941655#u32 1327108739#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (970822275 < 2147483647 ∧ 1360556665 < 2147483647) ∧ (861316228 < 2147483647 ∧ 129397094 < 2147483647); omega) canonical18 (by rfl)
#print axioms add18
theorem mul17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 68461852#u32 300409289#u32 928941655#u32 1327108739#u32) (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32)=ok (q 1606613093#u32 1387944829#u32 1303188230#u32 1380454753#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (68461852 < 2147483647 ∧ 300409289 < 2147483647) ∧ (928941655 < 2147483647 ∧ 1327108739 < 2147483647); omega) (by change (2023864416 < 2147483647 ∧ 983081232 < 2147483647) ∧ (187881185 < 2147483647 ∧ 1338388013 < 2147483647); omega) (by rfl)
#print axioms mul17
theorem add17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1606613093#u32 1387944829#u32 1303188230#u32 1380454753#u32) c17=ok (q 383594505#u32 1867989331#u32 793211865#u32 438405193#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1606613093 < 2147483647 ∧ 1387944829 < 2147483647) ∧ (1303188230 < 2147483647 ∧ 1380454753 < 2147483647); omega) canonical17 (by rfl)
#print axioms add17
theorem mul16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 383594505#u32 1867989331#u32 793211865#u32 438405193#u32) (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32)=ok (q 492125802#u32 1374364187#u32 950111159#u32 1121516683#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (383594505 < 2147483647 ∧ 1867989331 < 2147483647) ∧ (793211865 < 2147483647 ∧ 438405193 < 2147483647); omega) (by change (2023864416 < 2147483647 ∧ 983081232 < 2147483647) ∧ (187881185 < 2147483647 ∧ 1338388013 < 2147483647); omega) (by rfl)
#print axioms mul16
theorem add16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 492125802#u32 1374364187#u32 950111159#u32 1121516683#u32) c16=ok (q 790001514#u32 597212469#u32 728792975#u32 2061854650#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (492125802 < 2147483647 ∧ 1374364187 < 2147483647) ∧ (950111159 < 2147483647 ∧ 1121516683 < 2147483647); omega) canonical16 (by rfl)
#print axioms add16
theorem mul15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 790001514#u32 597212469#u32 728792975#u32 2061854650#u32) (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32)=ok (q 1473828071#u32 1535750311#u32 1003948965#u32 1007240933#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (790001514 < 2147483647 ∧ 597212469 < 2147483647) ∧ (728792975 < 2147483647 ∧ 2061854650 < 2147483647); omega) (by change (2023864416 < 2147483647 ∧ 983081232 < 2147483647) ∧ (187881185 < 2147483647 ∧ 1338388013 < 2147483647); omega) (by rfl)
#print axioms mul15
theorem add15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1473828071#u32 1535750311#u32 1003948965#u32 1007240933#u32) c15=ok (q 1942089378#u32 514813841#u32 1809045671#u32 1407612741#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1473828071 < 2147483647 ∧ 1535750311 < 2147483647) ∧ (1003948965 < 2147483647 ∧ 1007240933 < 2147483647); omega) canonical15 (by rfl)
#print axioms add15
theorem mul14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1942089378#u32 514813841#u32 1809045671#u32 1407612741#u32) (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32)=ok (q 1020749939#u32 1148216466#u32 1217340439#u32 427755229#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1942089378 < 2147483647 ∧ 514813841 < 2147483647) ∧ (1809045671 < 2147483647 ∧ 1407612741 < 2147483647); omega) (by change (2023864416 < 2147483647 ∧ 983081232 < 2147483647) ∧ (187881185 < 2147483647 ∧ 1338388013 < 2147483647); omega) (by rfl)
#print axioms mul14
theorem add14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1020749939#u32 1148216466#u32 1217340439#u32 427755229#u32) c14=ok (q 142518111#u32 1843244148#u32 1044278807#u32 1991755505#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1020749939 < 2147483647 ∧ 1148216466 < 2147483647) ∧ (1217340439 < 2147483647 ∧ 427755229 < 2147483647); omega) canonical14 (by rfl)
#print axioms add14
def final : Q := (q 142518111#u32 1843244148#u32 1044278807#u32 1991755505#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 7#usize 28#usize initial 14#usize final := by
  refine .step (by change 28>0; omega) (JFr_IndexArithmetic.sub 28#usize 27#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32) from rfl) mul27 (show Array.index_usize p 27#usize=ok c27 from rfl) add27 ?_
  refine .step (by change 27>0; omega) (JFr_IndexArithmetic.sub 27#usize 26#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32) from rfl) mul26 (show Array.index_usize p 26#usize=ok c26 from rfl) add26 ?_
  refine .step (by change 26>0; omega) (JFr_IndexArithmetic.sub 26#usize 25#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32) from rfl) mul25 (show Array.index_usize p 25#usize=ok c25 from rfl) add25 ?_
  refine .step (by change 25>0; omega) (JFr_IndexArithmetic.sub 25#usize 24#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32) from rfl) mul24 (show Array.index_usize p 24#usize=ok c24 from rfl) add24 ?_
  refine .step (by change 24>0; omega) (JFr_IndexArithmetic.sub 24#usize 23#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32) from rfl) mul23 (show Array.index_usize p 23#usize=ok c23 from rfl) add23 ?_
  refine .step (by change 23>0; omega) (JFr_IndexArithmetic.sub 23#usize 22#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32) from rfl) mul22 (show Array.index_usize p 22#usize=ok c22 from rfl) add22 ?_
  refine .step (by change 22>0; omega) (JFr_IndexArithmetic.sub 22#usize 21#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32) from rfl) mul21 (show Array.index_usize p 21#usize=ok c21 from rfl) add21 ?_
  refine .step (by change 21>0; omega) (JFr_IndexArithmetic.sub 21#usize 20#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32) from rfl) mul20 (show Array.index_usize p 20#usize=ok c20 from rfl) add20 ?_
  refine .step (by change 20>0; omega) (JFr_IndexArithmetic.sub 20#usize 19#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32) from rfl) mul19 (show Array.index_usize p 19#usize=ok c19 from rfl) add19 ?_
  refine .step (by change 19>0; omega) (JFr_IndexArithmetic.sub 19#usize 18#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32) from rfl) mul18 (show Array.index_usize p 18#usize=ok c18 from rfl) add18 ?_
  refine .step (by change 18>0; omega) (JFr_IndexArithmetic.sub 18#usize 17#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32) from rfl) mul17 (show Array.index_usize p 17#usize=ok c17 from rfl) add17 ?_
  refine .step (by change 17>0; omega) (JFr_IndexArithmetic.sub 17#usize 16#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32) from rfl) mul16 (show Array.index_usize p 16#usize=ok c16 from rfl) add16 ?_
  refine .step (by change 16>0; omega) (JFr_IndexArithmetic.sub 16#usize 15#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32) from rfl) mul15 (show Array.index_usize p 15#usize=ok c15 from rfl) add15 ?_
  refine .step (by change 15>0; omega) (JFr_IndexArithmetic.sub 15#usize 14#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32) from rfl) mul14 (show Array.index_usize p 14#usize=ok c14 from rfl) add14 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner07_0
