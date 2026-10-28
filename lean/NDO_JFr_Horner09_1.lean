import NDO_JFr_Data09
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner09_1
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data09
def initial : Q := (q 837512584#u32 1034806050#u32 1840833632#u32 1131458616#u32)
theorem mul13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 837512584#u32 1034806050#u32 1840833632#u32 1131458616#u32) (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32)=ok (q 1252215816#u32 154909048#u32 1437944638#u32 1412446659#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (837512584 < 2147483647 ∧ 1034806050 < 2147483647) ∧ (1840833632 < 2147483647 ∧ 1131458616 < 2147483647); omega) (by change (2030227143 < 2147483647 ∧ 1410410828 < 2147483647) ∧ (1902035786 < 2147483647 ∧ 62756635 < 2147483647); omega) (by rfl)
#print axioms mul13
theorem add13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1252215816#u32 154909048#u32 1437944638#u32 1412446659#u32) c13=ok (q 297909373#u32 2060706766#u32 1627478410#u32 152159414#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1252215816 < 2147483647 ∧ 154909048 < 2147483647) ∧ (1437944638 < 2147483647 ∧ 1412446659 < 2147483647); omega) canonical13 (by rfl)
#print axioms add13
theorem mul12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 297909373#u32 2060706766#u32 1627478410#u32 152159414#u32) (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32)=ok (q 706095535#u32 1662405963#u32 165680180#u32 475342043#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (297909373 < 2147483647 ∧ 2060706766 < 2147483647) ∧ (1627478410 < 2147483647 ∧ 152159414 < 2147483647); omega) (by change (2030227143 < 2147483647 ∧ 1410410828 < 2147483647) ∧ (1902035786 < 2147483647 ∧ 62756635 < 2147483647); omega) (by rfl)
#print axioms mul12
theorem add12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 706095535#u32 1662405963#u32 165680180#u32 475342043#u32) c12=ok (q 652917012#u32 702633270#u32 1338638593#u32 1070727129#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (706095535 < 2147483647 ∧ 1662405963 < 2147483647) ∧ (165680180 < 2147483647 ∧ 475342043 < 2147483647); omega) canonical12 (by rfl)
#print axioms add12
theorem mul11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 652917012#u32 702633270#u32 1338638593#u32 1070727129#u32) (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32)=ok (q 1930547401#u32 764021590#u32 2544396#u32 2072660641#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (652917012 < 2147483647 ∧ 702633270 < 2147483647) ∧ (1338638593 < 2147483647 ∧ 1070727129 < 2147483647); omega) (by change (2030227143 < 2147483647 ∧ 1410410828 < 2147483647) ∧ (1902035786 < 2147483647 ∧ 62756635 < 2147483647); omega) (by rfl)
#print axioms mul11
theorem add11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1930547401#u32 764021590#u32 2544396#u32 2072660641#u32) c11=ok (q 974518646#u32 352841287#u32 1522529562#u32 1507224756#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1930547401 < 2147483647 ∧ 764021590 < 2147483647) ∧ (2544396 < 2147483647 ∧ 2072660641 < 2147483647); omega) canonical11 (by rfl)
#print axioms add11
theorem mul10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 974518646#u32 352841287#u32 1522529562#u32 1507224756#u32) (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32)=ok (q 1580826137#u32 1826811707#u32 1260852930#u32 164893338#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (974518646 < 2147483647 ∧ 352841287 < 2147483647) ∧ (1522529562 < 2147483647 ∧ 1507224756 < 2147483647); omega) (by change (2030227143 < 2147483647 ∧ 1410410828 < 2147483647) ∧ (1902035786 < 2147483647 ∧ 62756635 < 2147483647); omega) (by rfl)
#print axioms mul10
theorem add10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1580826137#u32 1826811707#u32 1260852930#u32 164893338#u32) c10=ok (q 2141228533#u32 1798129377#u32 1902298701#u32 447944892#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1580826137 < 2147483647 ∧ 1826811707 < 2147483647) ∧ (1260852930 < 2147483647 ∧ 164893338 < 2147483647); omega) canonical10 (by rfl)
#print axioms add10
theorem mul09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2141228533#u32 1798129377#u32 1902298701#u32 447944892#u32) (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32)=ok (q 623105657#u32 1069067378#u32 1672890773#u32 1130699119#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2141228533 < 2147483647 ∧ 1798129377 < 2147483647) ∧ (1902298701 < 2147483647 ∧ 447944892 < 2147483647); omega) (by change (2030227143 < 2147483647 ∧ 1410410828 < 2147483647) ∧ (1902035786 < 2147483647 ∧ 62756635 < 2147483647); omega) (by rfl)
#print axioms mul09
theorem add09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 623105657#u32 1069067378#u32 1672890773#u32 1130699119#u32) c09=ok (q 1368166465#u32 1297765711#u32 271657735#u32 1877848806#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (623105657 < 2147483647 ∧ 1069067378 < 2147483647) ∧ (1672890773 < 2147483647 ∧ 1130699119 < 2147483647); omega) canonical09 (by rfl)
#print axioms add09
theorem mul08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1368166465#u32 1297765711#u32 271657735#u32 1877848806#u32) (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32)=ok (q 1830525630#u32 1629126669#u32 643914862#u32 399777297#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1368166465 < 2147483647 ∧ 1297765711 < 2147483647) ∧ (271657735 < 2147483647 ∧ 1877848806 < 2147483647); omega) (by change (2030227143 < 2147483647 ∧ 1410410828 < 2147483647) ∧ (1902035786 < 2147483647 ∧ 62756635 < 2147483647); omega) (by rfl)
#print axioms mul08
theorem add08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1830525630#u32 1629126669#u32 643914862#u32 399777297#u32) c08=ok (q 174999824#u32 1081523245#u32 1577137557#u32 1066293708#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1830525630 < 2147483647 ∧ 1629126669 < 2147483647) ∧ (643914862 < 2147483647 ∧ 399777297 < 2147483647); omega) canonical08 (by rfl)
#print axioms add08
theorem mul07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 174999824#u32 1081523245#u32 1577137557#u32 1066293708#u32) (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32)=ok (q 1995531487#u32 2122664544#u32 690960616#u32 608861053#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (174999824 < 2147483647 ∧ 1081523245 < 2147483647) ∧ (1577137557 < 2147483647 ∧ 1066293708 < 2147483647); omega) (by change (2030227143 < 2147483647 ∧ 1410410828 < 2147483647) ∧ (1902035786 < 2147483647 ∧ 62756635 < 2147483647); omega) (by rfl)
#print axioms mul07
theorem add07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1995531487#u32 2122664544#u32 690960616#u32 608861053#u32) c07=ok (q 1749971680#u32 875129133#u32 2118513430#u32 861776490#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1995531487 < 2147483647 ∧ 2122664544 < 2147483647) ∧ (690960616 < 2147483647 ∧ 608861053 < 2147483647); omega) canonical07 (by rfl)
#print axioms add07
theorem mul06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1749971680#u32 875129133#u32 2118513430#u32 861776490#u32) (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32)=ok (q 1018322142#u32 615527518#u32 1901204388#u32 1303340074#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1749971680 < 2147483647 ∧ 875129133 < 2147483647) ∧ (2118513430 < 2147483647 ∧ 861776490 < 2147483647); omega) (by change (2030227143 < 2147483647 ∧ 1410410828 < 2147483647) ∧ (1902035786 < 2147483647 ∧ 62756635 < 2147483647); omega) (by rfl)
#print axioms mul06
theorem add06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1018322142#u32 615527518#u32 1901204388#u32 1303340074#u32) c06=ok (q 593459708#u32 1997987066#u32 143296046#u32 1194522507#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1018322142 < 2147483647 ∧ 615527518 < 2147483647) ∧ (1901204388 < 2147483647 ∧ 1303340074 < 2147483647); omega) canonical06 (by rfl)
#print axioms add06
theorem mul05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 593459708#u32 1997987066#u32 143296046#u32 1194522507#u32) (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32)=ok (q 548083005#u32 1364097652#u32 1575269588#u32 1321996478#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (593459708 < 2147483647 ∧ 1997987066 < 2147483647) ∧ (143296046 < 2147483647 ∧ 1194522507 < 2147483647); omega) (by change (2030227143 < 2147483647 ∧ 1410410828 < 2147483647) ∧ (1902035786 < 2147483647 ∧ 62756635 < 2147483647); omega) (by rfl)
#print axioms mul05
theorem add05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 548083005#u32 1364097652#u32 1575269588#u32 1321996478#u32) c05=ok (q 1649050913#u32 1546265356#u32 1138711406#u32 553838045#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (548083005 < 2147483647 ∧ 1364097652 < 2147483647) ∧ (1575269588 < 2147483647 ∧ 1321996478 < 2147483647); omega) canonical05 (by rfl)
#print axioms add05
theorem mul04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1649050913#u32 1546265356#u32 1138711406#u32 553838045#u32) (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32)=ok (q 2133878753#u32 168878304#u32 799352891#u32 1535506001#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1649050913 < 2147483647 ∧ 1546265356 < 2147483647) ∧ (1138711406 < 2147483647 ∧ 553838045 < 2147483647); omega) (by change (2030227143 < 2147483647 ∧ 1410410828 < 2147483647) ∧ (1902035786 < 2147483647 ∧ 62756635 < 2147483647); omega) (by rfl)
#print axioms mul04
theorem add04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2133878753#u32 168878304#u32 799352891#u32 1535506001#u32) c04=ok (q 224703416#u32 2056461589#u32 345795715#u32 1486292097#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2133878753 < 2147483647 ∧ 168878304 < 2147483647) ∧ (799352891 < 2147483647 ∧ 1535506001 < 2147483647); omega) canonical04 (by rfl)
#print axioms add04
theorem mul03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 224703416#u32 2056461589#u32 345795715#u32 1486292097#u32) (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32)=ok (q 1336558627#u32 264890389#u32 1271567019#u32 648369012#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (224703416 < 2147483647 ∧ 2056461589 < 2147483647) ∧ (345795715 < 2147483647 ∧ 1486292097 < 2147483647); omega) (by change (2030227143 < 2147483647 ∧ 1410410828 < 2147483647) ∧ (1902035786 < 2147483647 ∧ 62756635 < 2147483647); omega) (by rfl)
#print axioms mul03
theorem add03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1336558627#u32 264890389#u32 1271567019#u32 648369012#u32) c03=ok (q 330101411#u32 669841303#u32 801639161#u32 454476539#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1336558627 < 2147483647 ∧ 264890389 < 2147483647) ∧ (1271567019 < 2147483647 ∧ 648369012 < 2147483647); omega) canonical03 (by rfl)
#print axioms add03
theorem mul02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 330101411#u32 669841303#u32 801639161#u32 454476539#u32) (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32)=ok (q 437914252#u32 1675169145#u32 2104168857#u32 1248182346#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (330101411 < 2147483647 ∧ 669841303 < 2147483647) ∧ (801639161 < 2147483647 ∧ 454476539 < 2147483647); omega) (by change (2030227143 < 2147483647 ∧ 1410410828 < 2147483647) ∧ (1902035786 < 2147483647 ∧ 62756635 < 2147483647); omega) (by rfl)
#print axioms mul02
theorem add02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 437914252#u32 1675169145#u32 2104168857#u32 1248182346#u32) c02=ok (q 797366126#u32 1703919393#u32 198095742#u32 1545193238#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (437914252 < 2147483647 ∧ 1675169145 < 2147483647) ∧ (2104168857 < 2147483647 ∧ 1248182346 < 2147483647); omega) canonical02 (by rfl)
#print axioms add02
theorem mul01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 797366126#u32 1703919393#u32 198095742#u32 1545193238#u32) (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32)=ok (q 1345837460#u32 730885440#u32 555387908#u32 1607544472#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (797366126 < 2147483647 ∧ 1703919393 < 2147483647) ∧ (198095742 < 2147483647 ∧ 1545193238 < 2147483647); omega) (by change (2030227143 < 2147483647 ∧ 1410410828 < 2147483647) ∧ (1902035786 < 2147483647 ∧ 62756635 < 2147483647); omega) (by rfl)
#print axioms mul01
theorem add01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1345837460#u32 730885440#u32 555387908#u32 1607544472#u32) c01=ok (q 59721972#u32 2082553886#u32 1154524224#u32 584411031#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1345837460 < 2147483647 ∧ 730885440 < 2147483647) ∧ (555387908 < 2147483647 ∧ 1607544472 < 2147483647); omega) canonical01 (by rfl)
#print axioms add01
theorem mul00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 59721972#u32 2082553886#u32 1154524224#u32 584411031#u32) (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32)=ok (q 1009830802#u32 765607002#u32 1739734872#u32 316183273#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (59721972 < 2147483647 ∧ 2082553886 < 2147483647) ∧ (1154524224 < 2147483647 ∧ 584411031 < 2147483647); omega) (by change (2030227143 < 2147483647 ∧ 1410410828 < 2147483647) ∧ (1902035786 < 2147483647 ∧ 62756635 < 2147483647); omega) (by rfl)
#print axioms mul00
theorem add00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1009830802#u32 765607002#u32 1739734872#u32 316183273#u32) c00=ok (q 1645475237#u32 1054917232#u32 2009538975#u32 558867101#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1009830802 < 2147483647 ∧ 765607002 < 2147483647) ∧ (1739734872 < 2147483647 ∧ 316183273 < 2147483647); omega) canonical00 (by rfl)
#print axioms add00
def final : Q := (q 1645475237#u32 1054917232#u32 2009538975#u32 558867101#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 9#usize 14#usize initial 0#usize final := by
  refine .step (by change 14>0; omega) (JFr_IndexArithmetic.sub 14#usize 13#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32) from rfl) mul13 (show Array.index_usize p 13#usize=ok c13 from rfl) add13 ?_
  refine .step (by change 13>0; omega) (JFr_IndexArithmetic.sub 13#usize 12#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32) from rfl) mul12 (show Array.index_usize p 12#usize=ok c12 from rfl) add12 ?_
  refine .step (by change 12>0; omega) (JFr_IndexArithmetic.sub 12#usize 11#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32) from rfl) mul11 (show Array.index_usize p 11#usize=ok c11 from rfl) add11 ?_
  refine .step (by change 11>0; omega) (JFr_IndexArithmetic.sub 11#usize 10#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32) from rfl) mul10 (show Array.index_usize p 10#usize=ok c10 from rfl) add10 ?_
  refine .step (by change 10>0; omega) (JFr_IndexArithmetic.sub 10#usize 9#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32) from rfl) mul09 (show Array.index_usize p 9#usize=ok c09 from rfl) add09 ?_
  refine .step (by change 9>0; omega) (JFr_IndexArithmetic.sub 9#usize 8#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32) from rfl) mul08 (show Array.index_usize p 8#usize=ok c08 from rfl) add08 ?_
  refine .step (by change 8>0; omega) (JFr_IndexArithmetic.sub 8#usize 7#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32) from rfl) mul07 (show Array.index_usize p 7#usize=ok c07 from rfl) add07 ?_
  refine .step (by change 7>0; omega) (JFr_IndexArithmetic.sub 7#usize 6#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32) from rfl) mul06 (show Array.index_usize p 6#usize=ok c06 from rfl) add06 ?_
  refine .step (by change 6>0; omega) (JFr_IndexArithmetic.sub 6#usize 5#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32) from rfl) mul05 (show Array.index_usize p 5#usize=ok c05 from rfl) add05 ?_
  refine .step (by change 5>0; omega) (JFr_IndexArithmetic.sub 5#usize 4#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32) from rfl) mul04 (show Array.index_usize p 4#usize=ok c04 from rfl) add04 ?_
  refine .step (by change 4>0; omega) (JFr_IndexArithmetic.sub 4#usize 3#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32) from rfl) mul03 (show Array.index_usize p 3#usize=ok c03 from rfl) add03 ?_
  refine .step (by change 3>0; omega) (JFr_IndexArithmetic.sub 3#usize 2#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32) from rfl) mul02 (show Array.index_usize p 2#usize=ok c02 from rfl) add02 ?_
  refine .step (by change 2>0; omega) (JFr_IndexArithmetic.sub 2#usize 1#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32) from rfl) mul01 (show Array.index_usize p 1#usize=ok c01 from rfl) add01 ?_
  refine .step (by change 1>0; omega) (JFr_IndexArithmetic.sub 1#usize 0#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 2030227143#u32 1410410828#u32 1902035786#u32 62756635#u32) from rfl) mul00 (show Array.index_usize p 0#usize=ok c00 from rfl) add00 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner09_1
