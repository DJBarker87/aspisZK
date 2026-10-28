import NDO_JFr_Data07
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner07_1
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data07
def initial : Q := (q 142518111#u32 1843244148#u32 1044278807#u32 1991755505#u32)
theorem mul13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 142518111#u32 1843244148#u32 1044278807#u32 1991755505#u32) (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32)=ok (q 373084360#u32 1722695794#u32 218159473#u32 352518044#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (142518111 < 2147483647 ∧ 1843244148 < 2147483647) ∧ (1044278807 < 2147483647 ∧ 1991755505 < 2147483647); omega) (by change (2023864416 < 2147483647 ∧ 983081232 < 2147483647) ∧ (187881185 < 2147483647 ∧ 1338388013 < 2147483647); omega) (by rfl)
#print axioms mul13
theorem add13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 373084360#u32 1722695794#u32 218159473#u32 352518044#u32) c13=ok (q 295265037#u32 1081349792#u32 1754107152#u32 421267581#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (373084360 < 2147483647 ∧ 1722695794 < 2147483647) ∧ (218159473 < 2147483647 ∧ 352518044 < 2147483647); omega) canonical13 (by rfl)
#print axioms add13
theorem mul12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 295265037#u32 1081349792#u32 1754107152#u32 421267581#u32) (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32)=ok (q 236616#u32 299631596#u32 1385191125#u32 175020285#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (295265037 < 2147483647 ∧ 1081349792 < 2147483647) ∧ (1754107152 < 2147483647 ∧ 421267581 < 2147483647); omega) (by change (2023864416 < 2147483647 ∧ 983081232 < 2147483647) ∧ (187881185 < 2147483647 ∧ 1338388013 < 2147483647); omega) (by rfl)
#print axioms mul12
theorem add12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 236616#u32 299631596#u32 1385191125#u32 175020285#u32) c12=ok (q 1576473215#u32 2015420390#u32 1853293725#u32 659584261#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (236616 < 2147483647 ∧ 299631596 < 2147483647) ∧ (1385191125 < 2147483647 ∧ 175020285 < 2147483647); omega) canonical12 (by rfl)
#print axioms add12
theorem mul11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1576473215#u32 2015420390#u32 1853293725#u32 659584261#u32) (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32)=ok (q 1719305966#u32 617705379#u32 1678962260#u32 1168302943#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1576473215 < 2147483647 ∧ 2015420390 < 2147483647) ∧ (1853293725 < 2147483647 ∧ 659584261 < 2147483647); omega) (by change (2023864416 < 2147483647 ∧ 983081232 < 2147483647) ∧ (187881185 < 2147483647 ∧ 1338388013 < 2147483647); omega) (by rfl)
#print axioms mul11
theorem add11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1719305966#u32 617705379#u32 1678962260#u32 1168302943#u32) c11=ok (q 1190695440#u32 998736298#u32 247084125#u32 196732858#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1719305966 < 2147483647 ∧ 617705379 < 2147483647) ∧ (1678962260 < 2147483647 ∧ 1168302943 < 2147483647); omega) canonical11 (by rfl)
#print axioms add11
theorem mul10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1190695440#u32 998736298#u32 247084125#u32 196732858#u32) (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32)=ok (q 50808902#u32 506981828#u32 1021256218#u32 692426599#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1190695440 < 2147483647 ∧ 998736298 < 2147483647) ∧ (247084125 < 2147483647 ∧ 196732858 < 2147483647); omega) (by change (2023864416 < 2147483647 ∧ 983081232 < 2147483647) ∧ (187881185 < 2147483647 ∧ 1338388013 < 2147483647); omega) (by rfl)
#print axioms mul10
theorem add10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 50808902#u32 506981828#u32 1021256218#u32 692426599#u32) c10=ok (q 1912270404#u32 1447113382#u32 1857355306#u32 1231539507#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (50808902 < 2147483647 ∧ 506981828 < 2147483647) ∧ (1021256218 < 2147483647 ∧ 692426599 < 2147483647); omega) canonical10 (by rfl)
#print axioms add10
theorem mul09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1912270404#u32 1447113382#u32 1857355306#u32 1231539507#u32) (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32)=ok (q 1890468681#u32 1543014922#u32 438577548#u32 1150980769#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1912270404 < 2147483647 ∧ 1447113382 < 2147483647) ∧ (1857355306 < 2147483647 ∧ 1231539507 < 2147483647); omega) (by change (2023864416 < 2147483647 ∧ 983081232 < 2147483647) ∧ (187881185 < 2147483647 ∧ 1338388013 < 2147483647); omega) (by rfl)
#print axioms mul09
theorem add09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1890468681#u32 1543014922#u32 438577548#u32 1150980769#u32) c09=ok (q 1583510840#u32 779332711#u32 116034936#u32 982257070#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1890468681 < 2147483647 ∧ 1543014922 < 2147483647) ∧ (438577548 < 2147483647 ∧ 1150980769 < 2147483647); omega) canonical09 (by rfl)
#print axioms add09
theorem mul08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1583510840#u32 779332711#u32 116034936#u32 982257070#u32) (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32)=ok (q 611931295#u32 1431152299#u32 1878132877#u32 997843829#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1583510840 < 2147483647 ∧ 779332711 < 2147483647) ∧ (116034936 < 2147483647 ∧ 982257070 < 2147483647); omega) (by change (2023864416 < 2147483647 ∧ 983081232 < 2147483647) ∧ (187881185 < 2147483647 ∧ 1338388013 < 2147483647); omega) (by rfl)
#print axioms mul08
theorem add08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 611931295#u32 1431152299#u32 1878132877#u32 997843829#u32) c08=ok (q 2108497406#u32 298793348#u32 527943043#u32 1389234213#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (611931295 < 2147483647 ∧ 1431152299 < 2147483647) ∧ (1878132877 < 2147483647 ∧ 997843829 < 2147483647); omega) canonical08 (by rfl)
#print axioms add08
theorem mul07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2108497406#u32 298793348#u32 527943043#u32 1389234213#u32) (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32)=ok (q 1640658255#u32 475840523#u32 1575719719#u32 360059018#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2108497406 < 2147483647 ∧ 298793348 < 2147483647) ∧ (527943043 < 2147483647 ∧ 1389234213 < 2147483647); omega) (by change (2023864416 < 2147483647 ∧ 983081232 < 2147483647) ∧ (187881185 < 2147483647 ∧ 1338388013 < 2147483647); omega) (by rfl)
#print axioms mul07
theorem add07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1640658255#u32 475840523#u32 1575719719#u32 360059018#u32) c07=ok (q 1012106745#u32 608345893#u32 690950682#u32 1874948992#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1640658255 < 2147483647 ∧ 475840523 < 2147483647) ∧ (1575719719 < 2147483647 ∧ 360059018 < 2147483647); omega) canonical07 (by rfl)
#print axioms add07
theorem mul06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1012106745#u32 608345893#u32 690950682#u32 1874948992#u32) (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32)=ok (q 1277396970#u32 1389756691#u32 1555703798#u32 1525479076#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1012106745 < 2147483647 ∧ 608345893 < 2147483647) ∧ (690950682 < 2147483647 ∧ 1874948992 < 2147483647); omega) (by change (2023864416 < 2147483647 ∧ 983081232 < 2147483647) ∧ (187881185 < 2147483647 ∧ 1338388013 < 2147483647); omega) (by rfl)
#print axioms mul06
theorem add06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1277396970#u32 1389756691#u32 1555703798#u32 1525479076#u32) c06=ok (q 1118523082#u32 219351972#u32 469903015#u32 1155978812#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1277396970 < 2147483647 ∧ 1389756691 < 2147483647) ∧ (1555703798 < 2147483647 ∧ 1525479076 < 2147483647); omega) canonical06 (by rfl)
#print axioms add06
theorem mul05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1118523082#u32 219351972#u32 469903015#u32 1155978812#u32) (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32)=ok (q 1323821929#u32 584796507#u32 1576458297#u32 2052456038#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1118523082 < 2147483647 ∧ 219351972 < 2147483647) ∧ (469903015 < 2147483647 ∧ 1155978812 < 2147483647); omega) (by change (2023864416 < 2147483647 ∧ 983081232 < 2147483647) ∧ (187881185 < 2147483647 ∧ 1338388013 < 2147483647); omega) (by rfl)
#print axioms mul05
theorem add05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1323821929#u32 584796507#u32 1576458297#u32 2052456038#u32) c05=ok (q 1290230885#u32 284814067#u32 1787097728#u32 258671921#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1323821929 < 2147483647 ∧ 584796507 < 2147483647) ∧ (1576458297 < 2147483647 ∧ 2052456038 < 2147483647); omega) canonical05 (by rfl)
#print axioms add05
theorem mul04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1290230885#u32 284814067#u32 1787097728#u32 258671921#u32) (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32)=ok (q 240603487#u32 404059634#u32 810267865#u32 69008935#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1290230885 < 2147483647 ∧ 284814067 < 2147483647) ∧ (1787097728 < 2147483647 ∧ 258671921 < 2147483647); omega) (by change (2023864416 < 2147483647 ∧ 983081232 < 2147483647) ∧ (187881185 < 2147483647 ∧ 1338388013 < 2147483647); omega) (by rfl)
#print axioms mul04
theorem add04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 240603487#u32 404059634#u32 810267865#u32 69008935#u32) c04=ok (q 99358821#u32 763827915#u32 1278622206#u32 641194429#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (240603487 < 2147483647 ∧ 404059634 < 2147483647) ∧ (810267865 < 2147483647 ∧ 69008935 < 2147483647); omega) canonical04 (by rfl)
#print axioms add04
theorem mul03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 99358821#u32 763827915#u32 1278622206#u32 641194429#u32) (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32)=ok (q 917767940#u32 258299895#u32 844906395#u32 1174319739#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (99358821 < 2147483647 ∧ 763827915 < 2147483647) ∧ (1278622206 < 2147483647 ∧ 641194429 < 2147483647); omega) (by change (2023864416 < 2147483647 ∧ 983081232 < 2147483647) ∧ (187881185 < 2147483647 ∧ 1338388013 < 2147483647); omega) (by rfl)
#print axioms mul03
theorem add03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 917767940#u32 258299895#u32 844906395#u32 1174319739#u32) c03=ok (q 67558493#u32 1919920878#u32 733220881#u32 1463342377#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (917767940 < 2147483647 ∧ 258299895 < 2147483647) ∧ (844906395 < 2147483647 ∧ 1174319739 < 2147483647); omega) canonical03 (by rfl)
#print axioms add03
theorem mul02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 67558493#u32 1919920878#u32 733220881#u32 1463342377#u32) (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32)=ok (q 1347234698#u32 3569131#u32 185932351#u32 1119645315#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (67558493 < 2147483647 ∧ 1919920878 < 2147483647) ∧ (733220881 < 2147483647 ∧ 1463342377 < 2147483647); omega) (by change (2023864416 < 2147483647 ∧ 983081232 < 2147483647) ∧ (187881185 < 2147483647 ∧ 1338388013 < 2147483647); omega) (by rfl)
#print axioms mul02
theorem add02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1347234698#u32 3569131#u32 185932351#u32 1119645315#u32) c02=ok (q 1429158080#u32 625555843#u32 1222477968#u32 1285082318#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1347234698 < 2147483647 ∧ 3569131 < 2147483647) ∧ (185932351 < 2147483647 ∧ 1119645315 < 2147483647); omega) canonical02 (by rfl)
#print axioms add02
theorem mul01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1429158080#u32 625555843#u32 1222477968#u32 1285082318#u32) (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32)=ok (q 1702972359#u32 1275172192#u32 1742551796#u32 338947136#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1429158080 < 2147483647 ∧ 625555843 < 2147483647) ∧ (1222477968 < 2147483647 ∧ 1285082318 < 2147483647); omega) (by change (2023864416 < 2147483647 ∧ 983081232 < 2147483647) ∧ (187881185 < 2147483647 ∧ 1338388013 < 2147483647); omega) (by rfl)
#print axioms mul01
theorem add01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1702972359#u32 1275172192#u32 1742551796#u32 338947136#u32) c01=ok (q 1132219155#u32 1374979901#u32 685454480#u32 1730594397#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1702972359 < 2147483647 ∧ 1275172192 < 2147483647) ∧ (1742551796 < 2147483647 ∧ 338947136 < 2147483647); omega) canonical01 (by rfl)
#print axioms add01
theorem mul00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1132219155#u32 1374979901#u32 685454480#u32 1730594397#u32) (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32)=ok (q 107219824#u32 806767789#u32 2004987978#u32 1676412762#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1132219155 < 2147483647 ∧ 1374979901 < 2147483647) ∧ (685454480 < 2147483647 ∧ 1730594397 < 2147483647); omega) (by change (2023864416 < 2147483647 ∧ 983081232 < 2147483647) ∧ (187881185 < 2147483647 ∧ 1338388013 < 2147483647); omega) (by rfl)
#print axioms mul00
theorem add00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 107219824#u32 806767789#u32 2004987978#u32 1676412762#u32) c00=ok (q 228735578#u32 775426259#u32 2109144676#u32 594800307#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (107219824 < 2147483647 ∧ 806767789 < 2147483647) ∧ (2004987978 < 2147483647 ∧ 1676412762 < 2147483647); omega) canonical00 (by rfl)
#print axioms add00
def final : Q := (q 228735578#u32 775426259#u32 2109144676#u32 594800307#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 7#usize 14#usize initial 0#usize final := by
  refine .step (by change 14>0; omega) (JFr_IndexArithmetic.sub 14#usize 13#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32) from rfl) mul13 (show Array.index_usize p 13#usize=ok c13 from rfl) add13 ?_
  refine .step (by change 13>0; omega) (JFr_IndexArithmetic.sub 13#usize 12#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32) from rfl) mul12 (show Array.index_usize p 12#usize=ok c12 from rfl) add12 ?_
  refine .step (by change 12>0; omega) (JFr_IndexArithmetic.sub 12#usize 11#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32) from rfl) mul11 (show Array.index_usize p 11#usize=ok c11 from rfl) add11 ?_
  refine .step (by change 11>0; omega) (JFr_IndexArithmetic.sub 11#usize 10#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32) from rfl) mul10 (show Array.index_usize p 10#usize=ok c10 from rfl) add10 ?_
  refine .step (by change 10>0; omega) (JFr_IndexArithmetic.sub 10#usize 9#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32) from rfl) mul09 (show Array.index_usize p 9#usize=ok c09 from rfl) add09 ?_
  refine .step (by change 9>0; omega) (JFr_IndexArithmetic.sub 9#usize 8#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32) from rfl) mul08 (show Array.index_usize p 8#usize=ok c08 from rfl) add08 ?_
  refine .step (by change 8>0; omega) (JFr_IndexArithmetic.sub 8#usize 7#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32) from rfl) mul07 (show Array.index_usize p 7#usize=ok c07 from rfl) add07 ?_
  refine .step (by change 7>0; omega) (JFr_IndexArithmetic.sub 7#usize 6#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32) from rfl) mul06 (show Array.index_usize p 6#usize=ok c06 from rfl) add06 ?_
  refine .step (by change 6>0; omega) (JFr_IndexArithmetic.sub 6#usize 5#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32) from rfl) mul05 (show Array.index_usize p 5#usize=ok c05 from rfl) add05 ?_
  refine .step (by change 5>0; omega) (JFr_IndexArithmetic.sub 5#usize 4#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32) from rfl) mul04 (show Array.index_usize p 4#usize=ok c04 from rfl) add04 ?_
  refine .step (by change 4>0; omega) (JFr_IndexArithmetic.sub 4#usize 3#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32) from rfl) mul03 (show Array.index_usize p 3#usize=ok c03 from rfl) add03 ?_
  refine .step (by change 3>0; omega) (JFr_IndexArithmetic.sub 3#usize 2#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32) from rfl) mul02 (show Array.index_usize p 2#usize=ok c02 from rfl) add02 ?_
  refine .step (by change 2>0; omega) (JFr_IndexArithmetic.sub 2#usize 1#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32) from rfl) mul01 (show Array.index_usize p 1#usize=ok c01 from rfl) add01 ?_
  refine .step (by change 1>0; omega) (JFr_IndexArithmetic.sub 1#usize 0#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 2023864416#u32 983081232#u32 187881185#u32 1338388013#u32) from rfl) mul00 (show Array.index_usize p 0#usize=ok c00 from rfl) add00 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner07_1
