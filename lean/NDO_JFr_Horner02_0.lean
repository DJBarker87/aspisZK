import NDO_JFr_Data02
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner02_0
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data02
def initial : Q := (q 0#u32 0#u32 0#u32 0#u32)
theorem mul27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 0#u32 0#u32 0#u32 0#u32) (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32)=ok (q 0#u32 0#u32 0#u32 0#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) (by change (1657509587 < 2147483647 ∧ 287924440 < 2147483647) ∧ (1819227394 < 2147483647 ∧ 1192254731 < 2147483647); omega) (by rfl)
#print axioms mul27
theorem add27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 0#u32 0#u32 0#u32 0#u32) c27=ok (q 1362014808#u32 2141505250#u32 1643976865#u32 1687810207#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) canonical27 (by rfl)
#print axioms add27
theorem mul26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1362014808#u32 2141505250#u32 1643976865#u32 1687810207#u32) (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32)=ok (q 976282707#u32 979003331#u32 237556927#u32 692256042#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1362014808 < 2147483647 ∧ 2141505250 < 2147483647) ∧ (1643976865 < 2147483647 ∧ 1687810207 < 2147483647); omega) (by change (1657509587 < 2147483647 ∧ 287924440 < 2147483647) ∧ (1819227394 < 2147483647 ∧ 1192254731 < 2147483647); omega) (by rfl)
#print axioms mul26
theorem add26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 976282707#u32 979003331#u32 237556927#u32 692256042#u32) c26=ok (q 1374612436#u32 1115537078#u32 1232405182#u32 1300076260#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (976282707 < 2147483647 ∧ 979003331 < 2147483647) ∧ (237556927 < 2147483647 ∧ 692256042 < 2147483647); omega) canonical26 (by rfl)
#print axioms add26
theorem mul25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1374612436#u32 1115537078#u32 1232405182#u32 1300076260#u32) (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32)=ok (q 194407118#u32 560581706#u32 1711303080#u32 1509123821#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1374612436 < 2147483647 ∧ 1115537078 < 2147483647) ∧ (1232405182 < 2147483647 ∧ 1300076260 < 2147483647); omega) (by change (1657509587 < 2147483647 ∧ 287924440 < 2147483647) ∧ (1819227394 < 2147483647 ∧ 1192254731 < 2147483647); omega) (by rfl)
#print axioms mul25
theorem add25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 194407118#u32 560581706#u32 1711303080#u32 1509123821#u32) c25=ok (q 1490954263#u32 1068334503#u32 533665065#u32 27761854#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (194407118 < 2147483647 ∧ 560581706 < 2147483647) ∧ (1711303080 < 2147483647 ∧ 1509123821 < 2147483647); omega) canonical25 (by rfl)
#print axioms add25
theorem mul24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1490954263#u32 1068334503#u32 533665065#u32 27761854#u32) (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32)=ok (q 131837031#u32 1371707744#u32 649107568#u32 1678273515#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1490954263 < 2147483647 ∧ 1068334503 < 2147483647) ∧ (533665065 < 2147483647 ∧ 27761854 < 2147483647); omega) (by change (1657509587 < 2147483647 ∧ 287924440 < 2147483647) ∧ (1819227394 < 2147483647 ∧ 1192254731 < 2147483647); omega) (by rfl)
#print axioms mul24
theorem add24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 131837031#u32 1371707744#u32 649107568#u32 1678273515#u32) c24=ok (q 59164878#u32 1188353335#u32 1519937832#u32 1248567203#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (131837031 < 2147483647 ∧ 1371707744 < 2147483647) ∧ (649107568 < 2147483647 ∧ 1678273515 < 2147483647); omega) canonical24 (by rfl)
#print axioms add24
theorem mul23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 59164878#u32 1188353335#u32 1519937832#u32 1248567203#u32) (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32)=ok (q 581955874#u32 476032171#u32 800160279#u32 247460839#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (59164878 < 2147483647 ∧ 1188353335 < 2147483647) ∧ (1519937832 < 2147483647 ∧ 1248567203 < 2147483647); omega) (by change (1657509587 < 2147483647 ∧ 287924440 < 2147483647) ∧ (1819227394 < 2147483647 ∧ 1192254731 < 2147483647); omega) (by rfl)
#print axioms mul23
theorem add23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 581955874#u32 476032171#u32 800160279#u32 247460839#u32) c23=ok (q 2137988881#u32 1166079689#u32 443424827#u32 1723722874#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (581955874 < 2147483647 ∧ 476032171 < 2147483647) ∧ (800160279 < 2147483647 ∧ 247460839 < 2147483647); omega) canonical23 (by rfl)
#print axioms add23
theorem mul22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2137988881#u32 1166079689#u32 443424827#u32 1723722874#u32) (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32)=ok (q 572522836#u32 1548103686#u32 14743425#u32 1025827613#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2137988881 < 2147483647 ∧ 1166079689 < 2147483647) ∧ (443424827 < 2147483647 ∧ 1723722874 < 2147483647); omega) (by change (1657509587 < 2147483647 ∧ 287924440 < 2147483647) ∧ (1819227394 < 2147483647 ∧ 1192254731 < 2147483647); omega) (by rfl)
#print axioms mul22
theorem add22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 572522836#u32 1548103686#u32 14743425#u32 1025827613#u32) c22=ok (q 268988421#u32 1127711365#u32 646513767#u32 1951690442#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (572522836 < 2147483647 ∧ 1548103686 < 2147483647) ∧ (14743425 < 2147483647 ∧ 1025827613 < 2147483647); omega) canonical22 (by rfl)
#print axioms add22
theorem mul21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 268988421#u32 1127711365#u32 646513767#u32 1951690442#u32) (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32)=ok (q 1429260443#u32 317932720#u32 1757792092#u32 1991998727#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (268988421 < 2147483647 ∧ 1127711365 < 2147483647) ∧ (646513767 < 2147483647 ∧ 1951690442 < 2147483647); omega) (by change (1657509587 < 2147483647 ∧ 287924440 < 2147483647) ∧ (1819227394 < 2147483647 ∧ 1192254731 < 2147483647); omega) (by rfl)
#print axioms mul21
theorem add21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1429260443#u32 317932720#u32 1757792092#u32 1991998727#u32) c21=ok (q 1126944716#u32 1522092697#u32 168976364#u32 479867653#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1429260443 < 2147483647 ∧ 317932720 < 2147483647) ∧ (1757792092 < 2147483647 ∧ 1991998727 < 2147483647); omega) canonical21 (by rfl)
#print axioms add21
theorem mul20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1126944716#u32 1522092697#u32 168976364#u32 479867653#u32) (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32)=ok (q 1029671132#u32 421840409#u32 18730140#u32 371655304#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1126944716 < 2147483647 ∧ 1522092697 < 2147483647) ∧ (168976364 < 2147483647 ∧ 479867653 < 2147483647); omega) (by change (1657509587 < 2147483647 ∧ 287924440 < 2147483647) ∧ (1819227394 < 2147483647 ∧ 1192254731 < 2147483647); omega) (by rfl)
#print axioms mul20
theorem add20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1029671132#u32 421840409#u32 18730140#u32 371655304#u32) c20=ok (q 2064256274#u32 887676358#u32 228872605#u32 489385424#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1029671132 < 2147483647 ∧ 421840409 < 2147483647) ∧ (18730140 < 2147483647 ∧ 371655304 < 2147483647); omega) canonical20 (by rfl)
#print axioms add20
theorem mul19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2064256274#u32 887676358#u32 228872605#u32 489385424#u32) (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32)=ok (q 1835076770#u32 947542430#u32 96188991#u32 1792382018#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2064256274 < 2147483647 ∧ 887676358 < 2147483647) ∧ (228872605 < 2147483647 ∧ 489385424 < 2147483647); omega) (by change (1657509587 < 2147483647 ∧ 287924440 < 2147483647) ∧ (1819227394 < 2147483647 ∧ 1192254731 < 2147483647); omega) (by rfl)
#print axioms mul19
theorem add19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1835076770#u32 947542430#u32 96188991#u32 1792382018#u32) c19=ok (q 192336792#u32 954761427#u32 701308746#u32 1585242055#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1835076770 < 2147483647 ∧ 947542430 < 2147483647) ∧ (96188991 < 2147483647 ∧ 1792382018 < 2147483647); omega) canonical19 (by rfl)
#print axioms add19
theorem mul18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 192336792#u32 954761427#u32 701308746#u32 1585242055#u32) (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32)=ok (q 1103772062#u32 1730776913#u32 1062078197#u32 1309595206#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (192336792 < 2147483647 ∧ 954761427 < 2147483647) ∧ (701308746 < 2147483647 ∧ 1585242055 < 2147483647); omega) (by change (1657509587 < 2147483647 ∧ 287924440 < 2147483647) ∧ (1819227394 < 2147483647 ∧ 1192254731 < 2147483647); omega) (by rfl)
#print axioms mul18
theorem add18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1103772062#u32 1730776913#u32 1062078197#u32 1309595206#u32) c18=ok (q 1936949372#u32 1027229041#u32 2088428291#u32 996767320#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1103772062 < 2147483647 ∧ 1730776913 < 2147483647) ∧ (1062078197 < 2147483647 ∧ 1309595206 < 2147483647); omega) canonical18 (by rfl)
#print axioms add18
theorem mul17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1936949372#u32 1027229041#u32 2088428291#u32 996767320#u32) (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32)=ok (q 435461508#u32 1576627656#u32 1033838678#u32 1393705970#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1936949372 < 2147483647 ∧ 1027229041 < 2147483647) ∧ (2088428291 < 2147483647 ∧ 996767320 < 2147483647); omega) (by change (1657509587 < 2147483647 ∧ 287924440 < 2147483647) ∧ (1819227394 < 2147483647 ∧ 1192254731 < 2147483647); omega) (by rfl)
#print axioms mul17
theorem add17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 435461508#u32 1576627656#u32 1033838678#u32 1393705970#u32) c17=ok (q 1211921872#u32 87038199#u32 20358492#u32 6482050#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (435461508 < 2147483647 ∧ 1576627656 < 2147483647) ∧ (1033838678 < 2147483647 ∧ 1393705970 < 2147483647); omega) canonical17 (by rfl)
#print axioms add17
theorem mul16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1211921872#u32 87038199#u32 20358492#u32 6482050#u32) (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32)=ok (q 519414512#u32 1119850551#u32 1981309725#u32 1454482353#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1211921872 < 2147483647 ∧ 87038199 < 2147483647) ∧ (20358492 < 2147483647 ∧ 6482050 < 2147483647); omega) (by change (1657509587 < 2147483647 ∧ 287924440 < 2147483647) ∧ (1819227394 < 2147483647 ∧ 1192254731 < 2147483647); omega) (by rfl)
#print axioms mul16
theorem add16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 519414512#u32 1119850551#u32 1981309725#u32 1454482353#u32) c16=ok (q 1571551310#u32 1472289122#u32 599081928#u32 253026898#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (519414512 < 2147483647 ∧ 1119850551 < 2147483647) ∧ (1981309725 < 2147483647 ∧ 1454482353 < 2147483647); omega) canonical16 (by rfl)
#print axioms add16
theorem mul15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1571551310#u32 1472289122#u32 599081928#u32 253026898#u32) (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32)=ok (q 1187604238#u32 426492062#u32 216854332#u32 1224547187#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1571551310 < 2147483647 ∧ 1472289122 < 2147483647) ∧ (599081928 < 2147483647 ∧ 253026898 < 2147483647); omega) (by change (1657509587 < 2147483647 ∧ 287924440 < 2147483647) ∧ (1819227394 < 2147483647 ∧ 1192254731 < 2147483647); omega) (by rfl)
#print axioms mul15
theorem add15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1187604238#u32 426492062#u32 216854332#u32 1224547187#u32) c15=ok (q 341999336#u32 2054082983#u32 893857264#u32 1145703312#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1187604238 < 2147483647 ∧ 426492062 < 2147483647) ∧ (216854332 < 2147483647 ∧ 1224547187 < 2147483647); omega) canonical15 (by rfl)
#print axioms add15
theorem mul14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 341999336#u32 2054082983#u32 893857264#u32 1145703312#u32) (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32)=ok (q 391050187#u32 953488965#u32 261036456#u32 1193129381#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (341999336 < 2147483647 ∧ 2054082983 < 2147483647) ∧ (893857264 < 2147483647 ∧ 1145703312 < 2147483647); omega) (by change (1657509587 < 2147483647 ∧ 287924440 < 2147483647) ∧ (1819227394 < 2147483647 ∧ 1192254731 < 2147483647); omega) (by rfl)
#print axioms mul14
theorem add14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 391050187#u32 953488965#u32 261036456#u32 1193129381#u32) c14=ok (q 1162182785#u32 1928795309#u32 804238543#u32 295474589#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (391050187 < 2147483647 ∧ 953488965 < 2147483647) ∧ (261036456 < 2147483647 ∧ 1193129381 < 2147483647); omega) canonical14 (by rfl)
#print axioms add14
def final : Q := (q 1162182785#u32 1928795309#u32 804238543#u32 295474589#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 2#usize 28#usize initial 14#usize final := by
  refine .step (by change 28>0; omega) (JFr_IndexArithmetic.sub 28#usize 27#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32) from rfl) mul27 (show Array.index_usize p 27#usize=ok c27 from rfl) add27 ?_
  refine .step (by change 27>0; omega) (JFr_IndexArithmetic.sub 27#usize 26#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32) from rfl) mul26 (show Array.index_usize p 26#usize=ok c26 from rfl) add26 ?_
  refine .step (by change 26>0; omega) (JFr_IndexArithmetic.sub 26#usize 25#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32) from rfl) mul25 (show Array.index_usize p 25#usize=ok c25 from rfl) add25 ?_
  refine .step (by change 25>0; omega) (JFr_IndexArithmetic.sub 25#usize 24#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32) from rfl) mul24 (show Array.index_usize p 24#usize=ok c24 from rfl) add24 ?_
  refine .step (by change 24>0; omega) (JFr_IndexArithmetic.sub 24#usize 23#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32) from rfl) mul23 (show Array.index_usize p 23#usize=ok c23 from rfl) add23 ?_
  refine .step (by change 23>0; omega) (JFr_IndexArithmetic.sub 23#usize 22#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32) from rfl) mul22 (show Array.index_usize p 22#usize=ok c22 from rfl) add22 ?_
  refine .step (by change 22>0; omega) (JFr_IndexArithmetic.sub 22#usize 21#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32) from rfl) mul21 (show Array.index_usize p 21#usize=ok c21 from rfl) add21 ?_
  refine .step (by change 21>0; omega) (JFr_IndexArithmetic.sub 21#usize 20#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32) from rfl) mul20 (show Array.index_usize p 20#usize=ok c20 from rfl) add20 ?_
  refine .step (by change 20>0; omega) (JFr_IndexArithmetic.sub 20#usize 19#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32) from rfl) mul19 (show Array.index_usize p 19#usize=ok c19 from rfl) add19 ?_
  refine .step (by change 19>0; omega) (JFr_IndexArithmetic.sub 19#usize 18#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32) from rfl) mul18 (show Array.index_usize p 18#usize=ok c18 from rfl) add18 ?_
  refine .step (by change 18>0; omega) (JFr_IndexArithmetic.sub 18#usize 17#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32) from rfl) mul17 (show Array.index_usize p 17#usize=ok c17 from rfl) add17 ?_
  refine .step (by change 17>0; omega) (JFr_IndexArithmetic.sub 17#usize 16#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32) from rfl) mul16 (show Array.index_usize p 16#usize=ok c16 from rfl) add16 ?_
  refine .step (by change 16>0; omega) (JFr_IndexArithmetic.sub 16#usize 15#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32) from rfl) mul15 (show Array.index_usize p 15#usize=ok c15 from rfl) add15 ?_
  refine .step (by change 15>0; omega) (JFr_IndexArithmetic.sub 15#usize 14#usize rfl) (show Array.index_usize alpha 2#usize=ok (q 1657509587#u32 287924440#u32 1819227394#u32 1192254731#u32) from rfl) mul14 (show Array.index_usize p 14#usize=ok c14 from rfl) add14 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner02_0
