import NDO_JFr_Data08
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner08_1
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data08
def initial : Q := (q 73961802#u32 2037623854#u32 1790073501#u32 1355316080#u32)
theorem mul13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 73961802#u32 2037623854#u32 1790073501#u32 1355316080#u32) (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32)=ok (q 1425429726#u32 940136268#u32 1413054350#u32 789860250#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (73961802 < 2147483647 ∧ 2037623854 < 2147483647) ∧ (1790073501 < 2147483647 ∧ 1355316080 < 2147483647); omega) (by change (454398981 < 2147483647 ∧ 504493626 < 2147483647) ∧ (2008082900 < 2147483647 ∧ 1252680230 < 2147483647); omega) (by rfl)
#print axioms mul13
theorem add13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1425429726#u32 940136268#u32 1413054350#u32 789860250#u32) c13=ok (q 2032666940#u32 1270739725#u32 1778225921#u32 921879029#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1425429726 < 2147483647 ∧ 940136268 < 2147483647) ∧ (1413054350 < 2147483647 ∧ 789860250 < 2147483647); omega) canonical13 (by rfl)
#print axioms add13
theorem mul12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2032666940#u32 1270739725#u32 1778225921#u32 921879029#u32) (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32)=ok (q 1019185629#u32 735531082#u32 938479908#u32 1972149736#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2032666940 < 2147483647 ∧ 1270739725 < 2147483647) ∧ (1778225921 < 2147483647 ∧ 921879029 < 2147483647); omega) (by change (454398981 < 2147483647 ∧ 504493626 < 2147483647) ∧ (2008082900 < 2147483647 ∧ 1252680230 < 2147483647); omega) (by rfl)
#print axioms mul12
theorem add12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1019185629#u32 735531082#u32 938479908#u32 1972149736#u32) c12=ok (q 1277751547#u32 1786198102#u32 491306484#u32 168255271#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1019185629 < 2147483647 ∧ 735531082 < 2147483647) ∧ (938479908 < 2147483647 ∧ 1972149736 < 2147483647); omega) canonical12 (by rfl)
#print axioms add12
theorem mul11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1277751547#u32 1786198102#u32 491306484#u32 168255271#u32) (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32)=ok (q 1718157228#u32 904731151#u32 938429243#u32 682631628#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1277751547 < 2147483647 ∧ 1786198102 < 2147483647) ∧ (491306484 < 2147483647 ∧ 168255271 < 2147483647); omega) (by change (454398981 < 2147483647 ∧ 504493626 < 2147483647) ∧ (2008082900 < 2147483647 ∧ 1252680230 < 2147483647); omega) (by rfl)
#print axioms mul11
theorem add11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1718157228#u32 904731151#u32 938429243#u32 682631628#u32) c11=ok (q 1715684924#u32 1319567452#u32 2019599961#u32 281061123#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1718157228 < 2147483647 ∧ 904731151 < 2147483647) ∧ (938429243 < 2147483647 ∧ 682631628 < 2147483647); omega) canonical11 (by rfl)
#print axioms add11
theorem mul10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1715684924#u32 1319567452#u32 2019599961#u32 281061123#u32) (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32)=ok (q 534865781#u32 1804211963#u32 1412123796#u32 215326701#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1715684924 < 2147483647 ∧ 1319567452 < 2147483647) ∧ (2019599961 < 2147483647 ∧ 281061123 < 2147483647); omega) (by change (454398981 < 2147483647 ∧ 504493626 < 2147483647) ∧ (2008082900 < 2147483647 ∧ 1252680230 < 2147483647); omega) (by rfl)
#print axioms mul10
theorem add10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 534865781#u32 1804211963#u32 1412123796#u32 215326701#u32) c10=ok (q 987259418#u32 1466482259#u32 910396105#u32 1128683174#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (534865781 < 2147483647 ∧ 1804211963 < 2147483647) ∧ (1412123796 < 2147483647 ∧ 215326701 < 2147483647); omega) canonical10 (by rfl)
#print axioms add10
theorem mul09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 987259418#u32 1466482259#u32 910396105#u32 1128683174#u32) (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32)=ok (q 1755044797#u32 1999427491#u32 1734194593#u32 1845693#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (987259418 < 2147483647 ∧ 1466482259 < 2147483647) ∧ (910396105 < 2147483647 ∧ 1128683174 < 2147483647); omega) (by change (454398981 < 2147483647 ∧ 504493626 < 2147483647) ∧ (2008082900 < 2147483647 ∧ 1252680230 < 2147483647); omega) (by rfl)
#print axioms mul09
theorem add09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1755044797#u32 1999427491#u32 1734194593#u32 1845693#u32) c09=ok (q 1972620463#u32 1435717958#u32 788771983#u32 495410344#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1755044797 < 2147483647 ∧ 1999427491 < 2147483647) ∧ (1734194593 < 2147483647 ∧ 1845693 < 2147483647); omega) canonical09 (by rfl)
#print axioms add09
theorem mul08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1972620463#u32 1435717958#u32 788771983#u32 495410344#u32) (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32)=ok (q 457856636#u32 665244990#u32 1072127199#u32 710202883#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1972620463 < 2147483647 ∧ 1435717958 < 2147483647) ∧ (788771983 < 2147483647 ∧ 495410344 < 2147483647); omega) (by change (454398981 < 2147483647 ∧ 504493626 < 2147483647) ∧ (2008082900 < 2147483647 ∧ 1252680230 < 2147483647); omega) (by rfl)
#print axioms mul08
theorem add08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 457856636#u32 665244990#u32 1072127199#u32 710202883#u32) c08=ok (q 499060907#u32 1806555365#u32 138854588#u32 680268588#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (457856636 < 2147483647 ∧ 665244990 < 2147483647) ∧ (1072127199 < 2147483647 ∧ 710202883 < 2147483647); omega) canonical08 (by rfl)
#print axioms add08
theorem mul07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 499060907#u32 1806555365#u32 138854588#u32 680268588#u32) (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32)=ok (q 634214435#u32 757345333#u32 158211266#u32 869449338#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (499060907 < 2147483647 ∧ 1806555365 < 2147483647) ∧ (138854588 < 2147483647 ∧ 680268588 < 2147483647); omega) (by change (454398981 < 2147483647 ∧ 504493626 < 2147483647) ∧ (2008082900 < 2147483647 ∧ 1252680230 < 2147483647); omega) (by rfl)
#print axioms mul07
theorem add07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 634214435#u32 757345333#u32 158211266#u32 869449338#u32) c07=ok (q 2081851575#u32 489172735#u32 66427329#u32 652973185#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (634214435 < 2147483647 ∧ 757345333 < 2147483647) ∧ (158211266 < 2147483647 ∧ 869449338 < 2147483647); omega) canonical07 (by rfl)
#print axioms add07
theorem mul06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2081851575#u32 489172735#u32 66427329#u32 652973185#u32) (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32)=ok (q 228884909#u32 2090463418#u32 1765105268#u32 832593193#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2081851575 < 2147483647 ∧ 489172735 < 2147483647) ∧ (66427329 < 2147483647 ∧ 652973185 < 2147483647); omega) (by change (454398981 < 2147483647 ∧ 504493626 < 2147483647) ∧ (2008082900 < 2147483647 ∧ 1252680230 < 2147483647); omega) (by rfl)
#print axioms mul06
theorem add06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 228884909#u32 2090463418#u32 1765105268#u32 832593193#u32) c06=ok (q 203776634#u32 752001131#u32 808320805#u32 77069081#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (228884909 < 2147483647 ∧ 2090463418 < 2147483647) ∧ (1765105268 < 2147483647 ∧ 832593193 < 2147483647); omega) canonical06 (by rfl)
#print axioms add06
theorem mul05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 203776634#u32 752001131#u32 808320805#u32 77069081#u32) (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32)=ok (q 156923768#u32 622768207#u32 1763570357#u32 1909010923#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (203776634 < 2147483647 ∧ 752001131 < 2147483647) ∧ (808320805 < 2147483647 ∧ 77069081 < 2147483647); omega) (by change (454398981 < 2147483647 ∧ 504493626 < 2147483647) ∧ (2008082900 < 2147483647 ∧ 1252680230 < 2147483647); omega) (by rfl)
#print axioms mul05
theorem add05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 156923768#u32 622768207#u32 1763570357#u32 1909010923#u32) c05=ok (q 1859376302#u32 1509578049#u32 1033349147#u32 758689365#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (156923768 < 2147483647 ∧ 622768207 < 2147483647) ∧ (1763570357 < 2147483647 ∧ 1909010923 < 2147483647); omega) canonical05 (by rfl)
#print axioms add05
theorem mul04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1859376302#u32 1509578049#u32 1033349147#u32 758689365#u32) (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32)=ok (q 1899509489#u32 1751324930#u32 278005914#u32 1549819376#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1859376302 < 2147483647 ∧ 1509578049 < 2147483647) ∧ (1033349147 < 2147483647 ∧ 758689365 < 2147483647); omega) (by change (454398981 < 2147483647 ∧ 504493626 < 2147483647) ∧ (2008082900 < 2147483647 ∧ 1252680230 < 2147483647); omega) (by rfl)
#print axioms mul04
theorem add04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1899509489#u32 1751324930#u32 278005914#u32 1549819376#u32) c04=ok (q 271889148#u32 398121381#u32 1188378781#u32 1429038249#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1899509489 < 2147483647 ∧ 1751324930 < 2147483647) ∧ (278005914 < 2147483647 ∧ 1549819376 < 2147483647); omega) canonical04 (by rfl)
#print axioms add04
theorem mul03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 271889148#u32 398121381#u32 1188378781#u32 1429038249#u32) (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32)=ok (q 265628622#u32 1652186358#u32 1006625438#u32 727004530#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (271889148 < 2147483647 ∧ 398121381 < 2147483647) ∧ (1188378781 < 2147483647 ∧ 1429038249 < 2147483647); omega) (by change (454398981 < 2147483647 ∧ 504493626 < 2147483647) ∧ (2008082900 < 2147483647 ∧ 1252680230 < 2147483647); omega) (by rfl)
#print axioms mul03
theorem add03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 265628622#u32 1652186358#u32 1006625438#u32 727004530#u32) c03=ok (q 1371899972#u32 1714567407#u32 739048255#u32 135015075#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (265628622 < 2147483647 ∧ 1652186358 < 2147483647) ∧ (1006625438 < 2147483647 ∧ 727004530 < 2147483647); omega) canonical03 (by rfl)
#print axioms add03
theorem mul02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1371899972#u32 1714567407#u32 739048255#u32 135015075#u32) (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32)=ok (q 1059773801#u32 530597690#u32 1170971342#u32 2105383071#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1371899972 < 2147483647 ∧ 1714567407 < 2147483647) ∧ (739048255 < 2147483647 ∧ 135015075 < 2147483647); omega) (by change (454398981 < 2147483647 ∧ 504493626 < 2147483647) ∧ (2008082900 < 2147483647 ∧ 1252680230 < 2147483647); omega) (by rfl)
#print axioms mul02
theorem add02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1059773801#u32 530597690#u32 1170971342#u32 2105383071#u32) c02=ok (q 198154152#u32 1797865277#u32 1453196835#u32 720776273#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1059773801 < 2147483647 ∧ 530597690 < 2147483647) ∧ (1170971342 < 2147483647 ∧ 2105383071 < 2147483647); omega) canonical02 (by rfl)
#print axioms add02
theorem mul01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 198154152#u32 1797865277#u32 1453196835#u32 720776273#u32) (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32)=ok (q 56068552#u32 791092316#u32 455362191#u32 1991703587#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (198154152 < 2147483647 ∧ 1797865277 < 2147483647) ∧ (1453196835 < 2147483647 ∧ 720776273 < 2147483647); omega) (by change (454398981 < 2147483647 ∧ 504493626 < 2147483647) ∧ (2008082900 < 2147483647 ∧ 1252680230 < 2147483647); omega) (by rfl)
#print axioms mul01
theorem add01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 56068552#u32 791092316#u32 455362191#u32 1991703587#u32) c01=ok (q 1130737113#u32 1225511732#u32 1349228519#u32 206604812#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (56068552 < 2147483647 ∧ 791092316 < 2147483647) ∧ (455362191 < 2147483647 ∧ 1991703587 < 2147483647); omega) canonical01 (by rfl)
#print axioms add01
theorem mul00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1130737113#u32 1225511732#u32 1349228519#u32 206604812#u32) (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32)=ok (q 1385811896#u32 1809915081#u32 305147511#u32 1689200202#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1130737113 < 2147483647 ∧ 1225511732 < 2147483647) ∧ (1349228519 < 2147483647 ∧ 206604812 < 2147483647); omega) (by change (454398981 < 2147483647 ∧ 504493626 < 2147483647) ∧ (2008082900 < 2147483647 ∧ 1252680230 < 2147483647); omega) (by rfl)
#print axioms mul00
theorem add00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1385811896#u32 1809915081#u32 305147511#u32 1689200202#u32) c00=ok (q 727390939#u32 532848710#u32 1194315987#u32 1329878310#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1385811896 < 2147483647 ∧ 1809915081 < 2147483647) ∧ (305147511 < 2147483647 ∧ 1689200202 < 2147483647); omega) canonical00 (by rfl)
#print axioms add00
def final : Q := (q 727390939#u32 532848710#u32 1194315987#u32 1329878310#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 8#usize 14#usize initial 0#usize final := by
  refine .step (by change 14>0; omega) (JFr_IndexArithmetic.sub 14#usize 13#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32) from rfl) mul13 (show Array.index_usize p 13#usize=ok c13 from rfl) add13 ?_
  refine .step (by change 13>0; omega) (JFr_IndexArithmetic.sub 13#usize 12#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32) from rfl) mul12 (show Array.index_usize p 12#usize=ok c12 from rfl) add12 ?_
  refine .step (by change 12>0; omega) (JFr_IndexArithmetic.sub 12#usize 11#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32) from rfl) mul11 (show Array.index_usize p 11#usize=ok c11 from rfl) add11 ?_
  refine .step (by change 11>0; omega) (JFr_IndexArithmetic.sub 11#usize 10#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32) from rfl) mul10 (show Array.index_usize p 10#usize=ok c10 from rfl) add10 ?_
  refine .step (by change 10>0; omega) (JFr_IndexArithmetic.sub 10#usize 9#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32) from rfl) mul09 (show Array.index_usize p 9#usize=ok c09 from rfl) add09 ?_
  refine .step (by change 9>0; omega) (JFr_IndexArithmetic.sub 9#usize 8#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32) from rfl) mul08 (show Array.index_usize p 8#usize=ok c08 from rfl) add08 ?_
  refine .step (by change 8>0; omega) (JFr_IndexArithmetic.sub 8#usize 7#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32) from rfl) mul07 (show Array.index_usize p 7#usize=ok c07 from rfl) add07 ?_
  refine .step (by change 7>0; omega) (JFr_IndexArithmetic.sub 7#usize 6#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32) from rfl) mul06 (show Array.index_usize p 6#usize=ok c06 from rfl) add06 ?_
  refine .step (by change 6>0; omega) (JFr_IndexArithmetic.sub 6#usize 5#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32) from rfl) mul05 (show Array.index_usize p 5#usize=ok c05 from rfl) add05 ?_
  refine .step (by change 5>0; omega) (JFr_IndexArithmetic.sub 5#usize 4#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32) from rfl) mul04 (show Array.index_usize p 4#usize=ok c04 from rfl) add04 ?_
  refine .step (by change 4>0; omega) (JFr_IndexArithmetic.sub 4#usize 3#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32) from rfl) mul03 (show Array.index_usize p 3#usize=ok c03 from rfl) add03 ?_
  refine .step (by change 3>0; omega) (JFr_IndexArithmetic.sub 3#usize 2#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32) from rfl) mul02 (show Array.index_usize p 2#usize=ok c02 from rfl) add02 ?_
  refine .step (by change 2>0; omega) (JFr_IndexArithmetic.sub 2#usize 1#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32) from rfl) mul01 (show Array.index_usize p 1#usize=ok c01 from rfl) add01 ?_
  refine .step (by change 1>0; omega) (JFr_IndexArithmetic.sub 1#usize 0#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 454398981#u32 504493626#u32 2008082900#u32 1252680230#u32) from rfl) mul00 (show Array.index_usize p 0#usize=ok c00 from rfl) add00 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner08_1
