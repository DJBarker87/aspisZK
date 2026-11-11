import NDO_JFr_Data07
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner07_1
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data07
def initial : Q := (q 828515149#u32 1665862388#u32 987748807#u32 1524896543#u32)
theorem mul13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 828515149#u32 1665862388#u32 987748807#u32 1524896543#u32) (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32)=ok (q 966944267#u32 967387156#u32 1230411857#u32 173076335#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (828515149 < 2147483647 ∧ 1665862388 < 2147483647) ∧ (987748807 < 2147483647 ∧ 1524896543 < 2147483647); omega) (by change (562817633 < 2147483647 ∧ 1940768295 < 2147483647) ∧ (892660560 < 2147483647 ∧ 287439637 < 2147483647); omega) (by rfl)
#print axioms mul13
theorem add13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 966944267#u32 967387156#u32 1230411857#u32 173076335#u32) c13=ok (q 1135298667#u32 2018517879#u32 1279820033#u32 332529442#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (966944267 < 2147483647 ∧ 967387156 < 2147483647) ∧ (1230411857 < 2147483647 ∧ 173076335 < 2147483647); omega) canonical13 (by rfl)
#print axioms add13
theorem mul12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1135298667#u32 2018517879#u32 1279820033#u32 332529442#u32) (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32)=ok (q 1250807670#u32 948985095#u32 449492587#u32 646872586#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1135298667 < 2147483647 ∧ 2018517879 < 2147483647) ∧ (1279820033 < 2147483647 ∧ 332529442 < 2147483647); omega) (by change (562817633 < 2147483647 ∧ 1940768295 < 2147483647) ∧ (892660560 < 2147483647 ∧ 287439637 < 2147483647); omega) (by rfl)
#print axioms mul12
theorem add12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1250807670#u32 948985095#u32 449492587#u32 646872586#u32) c12=ok (q 1947827370#u32 7046327#u32 1043418679#u32 1816238362#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1250807670 < 2147483647 ∧ 948985095 < 2147483647) ∧ (449492587 < 2147483647 ∧ 646872586 < 2147483647); omega) canonical12 (by rfl)
#print axioms add12
theorem mul11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1947827370#u32 7046327#u32 1043418679#u32 1816238362#u32) (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32)=ok (q 798442075#u32 846682356#u32 740368388#u32 305625538#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1947827370 < 2147483647 ∧ 7046327 < 2147483647) ∧ (1043418679 < 2147483647 ∧ 1816238362 < 2147483647); omega) (by change (562817633 < 2147483647 ∧ 1940768295 < 2147483647) ∧ (892660560 < 2147483647 ∧ 287439637 < 2147483647); omega) (by rfl)
#print axioms mul11
theorem add11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 798442075#u32 846682356#u32 740368388#u32 305625538#u32) c11=ok (q 2037017001#u32 1174839279#u32 1962639916#u32 703720133#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (798442075 < 2147483647 ∧ 846682356 < 2147483647) ∧ (740368388 < 2147483647 ∧ 305625538 < 2147483647); omega) canonical11 (by rfl)
#print axioms add11
theorem mul10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2037017001#u32 1174839279#u32 1962639916#u32 703720133#u32) (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32)=ok (q 1041185565#u32 1654420047#u32 1742688974#u32 730968115#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2037017001 < 2147483647 ∧ 1174839279 < 2147483647) ∧ (1962639916 < 2147483647 ∧ 703720133 < 2147483647); omega) (by change (562817633 < 2147483647 ∧ 1940768295 < 2147483647) ∧ (892660560 < 2147483647 ∧ 287439637 < 2147483647); omega) (by rfl)
#print axioms mul10
theorem add10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1041185565#u32 1654420047#u32 1742688974#u32 730968115#u32) c10=ok (q 1749870321#u32 1767391992#u32 539945659#u32 330121451#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1041185565 < 2147483647 ∧ 1654420047 < 2147483647) ∧ (1742688974 < 2147483647 ∧ 730968115 < 2147483647); omega) canonical10 (by rfl)
#print axioms add10
theorem mul09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1749870321#u32 1767391992#u32 539945659#u32 330121451#u32) (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32)=ok (q 1488951243#u32 2100529537#u32 2105157321#u32 685876013#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1749870321 < 2147483647 ∧ 1767391992 < 2147483647) ∧ (539945659 < 2147483647 ∧ 330121451 < 2147483647); omega) (by change (562817633 < 2147483647 ∧ 1940768295 < 2147483647) ∧ (892660560 < 2147483647 ∧ 287439637 < 2147483647); omega) (by rfl)
#print axioms mul09
theorem add09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1488951243#u32 2100529537#u32 2105157321#u32 685876013#u32) c09=ok (q 541670975#u32 1045926455#u32 720883801#u32 1499060470#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1488951243 < 2147483647 ∧ 2100529537 < 2147483647) ∧ (2105157321 < 2147483647 ∧ 685876013 < 2147483647); omega) canonical09 (by rfl)
#print axioms add09
theorem mul08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 541670975#u32 1045926455#u32 720883801#u32 1499060470#u32) (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32)=ok (q 1072814843#u32 1632806615#u32 1941285590#u32 2036324374#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (541670975 < 2147483647 ∧ 1045926455 < 2147483647) ∧ (720883801 < 2147483647 ∧ 1499060470 < 2147483647); omega) (by change (562817633 < 2147483647 ∧ 1940768295 < 2147483647) ∧ (892660560 < 2147483647 ∧ 287439637 < 2147483647); omega) (by rfl)
#print axioms mul08
theorem add08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1072814843#u32 1632806615#u32 1941285590#u32 2036324374#u32) c08=ok (q 937965295#u32 1717837856#u32 1188920309#u32 363568823#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1072814843 < 2147483647 ∧ 1632806615 < 2147483647) ∧ (1941285590 < 2147483647 ∧ 2036324374 < 2147483647); omega) canonical08 (by rfl)
#print axioms add08
theorem mul07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 937965295#u32 1717837856#u32 1188920309#u32 363568823#u32) (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32)=ok (q 153795623#u32 285409372#u32 686390294#u32 90809524#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (937965295 < 2147483647 ∧ 1717837856 < 2147483647) ∧ (1188920309 < 2147483647 ∧ 363568823 < 2147483647); omega) (by change (562817633 < 2147483647 ∧ 1940768295 < 2147483647) ∧ (892660560 < 2147483647 ∧ 287439637 < 2147483647); omega) (by rfl)
#print axioms mul07
theorem add07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 153795623#u32 285409372#u32 686390294#u32 90809524#u32) c07=ok (q 1824744525#u32 645374250#u32 1716756092#u32 1101435411#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (153795623 < 2147483647 ∧ 285409372 < 2147483647) ∧ (686390294 < 2147483647 ∧ 90809524 < 2147483647); omega) canonical07 (by rfl)
#print axioms add07
theorem mul06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1824744525#u32 645374250#u32 1716756092#u32 1101435411#u32) (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32)=ok (q 657922358#u32 1004313717#u32 1472362724#u32 1366518834#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1824744525 < 2147483647 ∧ 645374250 < 2147483647) ∧ (1716756092 < 2147483647 ∧ 1101435411 < 2147483647); omega) (by change (562817633 < 2147483647 ∧ 1940768295 < 2147483647) ∧ (892660560 < 2147483647 ∧ 287439637 < 2147483647); omega) (by rfl)
#print axioms mul06
theorem add06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 657922358#u32 1004313717#u32 1472362724#u32 1366518834#u32) c06=ok (q 1440669337#u32 594204488#u32 1412111048#u32 10277233#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (657922358 < 2147483647 ∧ 1004313717 < 2147483647) ∧ (1472362724 < 2147483647 ∧ 1366518834 < 2147483647); omega) canonical06 (by rfl)
#print axioms add06
theorem mul05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1440669337#u32 594204488#u32 1412111048#u32 10277233#u32) (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32)=ok (q 39224881#u32 1328598355#u32 1116733235#u32 251424125#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1440669337 < 2147483647 ∧ 594204488 < 2147483647) ∧ (1412111048 < 2147483647 ∧ 10277233 < 2147483647); omega) (by change (562817633 < 2147483647 ∧ 1940768295 < 2147483647) ∧ (892660560 < 2147483647 ∧ 287439637 < 2147483647); omega) (by rfl)
#print axioms mul05
theorem add05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 39224881#u32 1328598355#u32 1116733235#u32 251424125#u32) c05=ok (q 1225528353#u32 854922425#u32 634672355#u32 1754400811#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (39224881 < 2147483647 ∧ 1328598355 < 2147483647) ∧ (1116733235 < 2147483647 ∧ 251424125 < 2147483647); omega) canonical05 (by rfl)
#print axioms add05
theorem mul04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1225528353#u32 854922425#u32 634672355#u32 1754400811#u32) (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32)=ok (q 913742187#u32 92793952#u32 961590111#u32 1296421956#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1225528353 < 2147483647 ∧ 854922425 < 2147483647) ∧ (634672355 < 2147483647 ∧ 1754400811 < 2147483647); omega) (by change (562817633 < 2147483647 ∧ 1940768295 < 2147483647) ∧ (892660560 < 2147483647 ∧ 287439637 < 2147483647); omega) (by rfl)
#print axioms mul04
theorem add04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 913742187#u32 92793952#u32 961590111#u32 1296421956#u32) c04=ok (q 989805732#u32 671176552#u32 943304092#u32 869108774#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (913742187 < 2147483647 ∧ 92793952 < 2147483647) ∧ (961590111 < 2147483647 ∧ 1296421956 < 2147483647); omega) canonical04 (by rfl)
#print axioms add04
theorem mul03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 989805732#u32 671176552#u32 943304092#u32 869108774#u32) (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32)=ok (q 174094690#u32 1158971347#u32 1870174539#u32 1062595624#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (989805732 < 2147483647 ∧ 671176552 < 2147483647) ∧ (943304092 < 2147483647 ∧ 869108774 < 2147483647); omega) (by change (562817633 < 2147483647 ∧ 1940768295 < 2147483647) ∧ (892660560 < 2147483647 ∧ 287439637 < 2147483647); omega) (by rfl)
#print axioms mul03
theorem add03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 174094690#u32 1158971347#u32 1870174539#u32 1062595624#u32) c03=ok (q 1122316741#u32 284858325#u32 767994365#u32 61602954#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (174094690 < 2147483647 ∧ 1158971347 < 2147483647) ∧ (1870174539 < 2147483647 ∧ 1062595624 < 2147483647); omega) canonical03 (by rfl)
#print axioms add03
theorem mul02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1122316741#u32 284858325#u32 767994365#u32 61602954#u32) (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32)=ok (q 1781834285#u32 369854295#u32 568792040#u32 1609536781#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1122316741 < 2147483647 ∧ 284858325 < 2147483647) ∧ (767994365 < 2147483647 ∧ 61602954 < 2147483647); omega) (by change (562817633 < 2147483647 ∧ 1940768295 < 2147483647) ∧ (892660560 < 2147483647 ∧ 287439637 < 2147483647); omega) (by rfl)
#print axioms mul02
theorem add02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1781834285#u32 369854295#u32 568792040#u32 1609536781#u32) c02=ok (q 455806099#u32 1789335572#u32 307811769#u32 552034774#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1781834285 < 2147483647 ∧ 369854295 < 2147483647) ∧ (568792040 < 2147483647 ∧ 1609536781 < 2147483647); omega) canonical02 (by rfl)
#print axioms add02
theorem mul01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 455806099#u32 1789335572#u32 307811769#u32 552034774#u32) (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32)=ok (q 903950910#u32 1382019199#u32 855304076#u32 277081033#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (455806099 < 2147483647 ∧ 1789335572 < 2147483647) ∧ (307811769 < 2147483647 ∧ 552034774 < 2147483647); omega) (by change (562817633 < 2147483647 ∧ 1940768295 < 2147483647) ∧ (892660560 < 2147483647 ∧ 287439637 < 2147483647); omega) (by rfl)
#print axioms mul01
theorem add01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 903950910#u32 1382019199#u32 855304076#u32 277081033#u32) c01=ok (q 2046869124#u32 38316378#u32 1507682405#u32 2036744974#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (903950910 < 2147483647 ∧ 1382019199 < 2147483647) ∧ (855304076 < 2147483647 ∧ 277081033 < 2147483647); omega) canonical01 (by rfl)
#print axioms add01
theorem mul00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2046869124#u32 38316378#u32 1507682405#u32 2036744974#u32) (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32)=ok (q 1411951651#u32 389126435#u32 1725138247#u32 251613718#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2046869124 < 2147483647 ∧ 38316378 < 2147483647) ∧ (1507682405 < 2147483647 ∧ 2036744974 < 2147483647); omega) (by change (562817633 < 2147483647 ∧ 1940768295 < 2147483647) ∧ (892660560 < 2147483647 ∧ 287439637 < 2147483647); omega) (by rfl)
#print axioms mul00
theorem add00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1411951651#u32 389126435#u32 1725138247#u32 251613718#u32) c00=ok (q 537832710#u32 1523139272#u32 1329512139#u32 1688946054#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1411951651 < 2147483647 ∧ 389126435 < 2147483647) ∧ (1725138247 < 2147483647 ∧ 251613718 < 2147483647); omega) canonical00 (by rfl)
#print axioms add00
def final : Q := (q 537832710#u32 1523139272#u32 1329512139#u32 1688946054#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 7#usize 14#usize initial 0#usize final := by
  refine .step (by change 14>0; omega) (JFr_IndexArithmetic.sub 14#usize 13#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32) from rfl) mul13 (show Array.index_usize p 13#usize=ok c13 from rfl) add13 ?_
  refine .step (by change 13>0; omega) (JFr_IndexArithmetic.sub 13#usize 12#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32) from rfl) mul12 (show Array.index_usize p 12#usize=ok c12 from rfl) add12 ?_
  refine .step (by change 12>0; omega) (JFr_IndexArithmetic.sub 12#usize 11#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32) from rfl) mul11 (show Array.index_usize p 11#usize=ok c11 from rfl) add11 ?_
  refine .step (by change 11>0; omega) (JFr_IndexArithmetic.sub 11#usize 10#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32) from rfl) mul10 (show Array.index_usize p 10#usize=ok c10 from rfl) add10 ?_
  refine .step (by change 10>0; omega) (JFr_IndexArithmetic.sub 10#usize 9#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32) from rfl) mul09 (show Array.index_usize p 9#usize=ok c09 from rfl) add09 ?_
  refine .step (by change 9>0; omega) (JFr_IndexArithmetic.sub 9#usize 8#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32) from rfl) mul08 (show Array.index_usize p 8#usize=ok c08 from rfl) add08 ?_
  refine .step (by change 8>0; omega) (JFr_IndexArithmetic.sub 8#usize 7#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32) from rfl) mul07 (show Array.index_usize p 7#usize=ok c07 from rfl) add07 ?_
  refine .step (by change 7>0; omega) (JFr_IndexArithmetic.sub 7#usize 6#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32) from rfl) mul06 (show Array.index_usize p 6#usize=ok c06 from rfl) add06 ?_
  refine .step (by change 6>0; omega) (JFr_IndexArithmetic.sub 6#usize 5#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32) from rfl) mul05 (show Array.index_usize p 5#usize=ok c05 from rfl) add05 ?_
  refine .step (by change 5>0; omega) (JFr_IndexArithmetic.sub 5#usize 4#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32) from rfl) mul04 (show Array.index_usize p 4#usize=ok c04 from rfl) add04 ?_
  refine .step (by change 4>0; omega) (JFr_IndexArithmetic.sub 4#usize 3#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32) from rfl) mul03 (show Array.index_usize p 3#usize=ok c03 from rfl) add03 ?_
  refine .step (by change 3>0; omega) (JFr_IndexArithmetic.sub 3#usize 2#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32) from rfl) mul02 (show Array.index_usize p 2#usize=ok c02 from rfl) add02 ?_
  refine .step (by change 2>0; omega) (JFr_IndexArithmetic.sub 2#usize 1#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32) from rfl) mul01 (show Array.index_usize p 1#usize=ok c01 from rfl) add01 ?_
  refine .step (by change 1>0; omega) (JFr_IndexArithmetic.sub 1#usize 0#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32) from rfl) mul00 (show Array.index_usize p 0#usize=ok c00 from rfl) add00 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner07_1
