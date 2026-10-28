import NDO_JFr_Data01
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner01_1
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data01
def initial : Q := (q 1299681090#u32 731504958#u32 196634121#u32 1544879166#u32)
theorem mul13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1299681090#u32 731504958#u32 196634121#u32 1544879166#u32) (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32)=ok (q 540566545#u32 250398445#u32 1941215601#u32 523644587#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1299681090 < 2147483647 ∧ 731504958 < 2147483647) ∧ (196634121 < 2147483647 ∧ 1544879166 < 2147483647); omega) (by change (528783666 < 2147483647 ∧ 1672539309 < 2147483647) ∧ (1274387717 < 2147483647 ∧ 552414171 < 2147483647); omega) (by rfl)
#print axioms mul13
theorem add13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 540566545#u32 250398445#u32 1941215601#u32 523644587#u32) c13=ok (q 1725882152#u32 421903202#u32 1593973309#u32 417971804#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (540566545 < 2147483647 ∧ 250398445 < 2147483647) ∧ (1941215601 < 2147483647 ∧ 523644587 < 2147483647); omega) canonical13 (by rfl)
#print axioms add13
theorem mul12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1725882152#u32 421903202#u32 1593973309#u32 417971804#u32) (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32)=ok (q 371594709#u32 32407120#u32 393079665#u32 1334481334#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1725882152 < 2147483647 ∧ 421903202 < 2147483647) ∧ (1593973309 < 2147483647 ∧ 417971804 < 2147483647); omega) (by change (528783666 < 2147483647 ∧ 1672539309 < 2147483647) ∧ (1274387717 < 2147483647 ∧ 552414171 < 2147483647); omega) (by rfl)
#print axioms mul12
theorem add12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 371594709#u32 32407120#u32 393079665#u32 1334481334#u32) c12=ok (q 1555421803#u32 1386507406#u32 1618088859#u32 1877821908#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (371594709 < 2147483647 ∧ 32407120 < 2147483647) ∧ (393079665 < 2147483647 ∧ 1334481334 < 2147483647); omega) canonical12 (by rfl)
#print axioms add12
theorem mul11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1555421803#u32 1386507406#u32 1618088859#u32 1877821908#u32) (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32)=ok (q 255293476#u32 12976429#u32 1302582272#u32 1058236964#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1555421803 < 2147483647 ∧ 1386507406 < 2147483647) ∧ (1618088859 < 2147483647 ∧ 1877821908 < 2147483647); omega) (by change (528783666 < 2147483647 ∧ 1672539309 < 2147483647) ∧ (1274387717 < 2147483647 ∧ 552414171 < 2147483647); omega) (by rfl)
#print axioms mul11
theorem add11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 255293476#u32 12976429#u32 1302582272#u32 1058236964#u32) c11=ok (q 1617142552#u32 106400059#u32 180092830#u32 1427214378#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (255293476 < 2147483647 ∧ 12976429 < 2147483647) ∧ (1302582272 < 2147483647 ∧ 1058236964 < 2147483647); omega) canonical11 (by rfl)
#print axioms add11
theorem mul10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1617142552#u32 106400059#u32 180092830#u32 1427214378#u32) (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32)=ok (q 397140113#u32 986979750#u32 1638334236#u32 1167960466#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1617142552 < 2147483647 ∧ 106400059 < 2147483647) ∧ (180092830 < 2147483647 ∧ 1427214378 < 2147483647); omega) (by change (528783666 < 2147483647 ∧ 1672539309 < 2147483647) ∧ (1274387717 < 2147483647 ∧ 552414171 < 2147483647); omega) (by rfl)
#print axioms mul10
theorem add10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 397140113#u32 986979750#u32 1638334236#u32 1167960466#u32) c10=ok (q 1456048369#u32 1529875538#u32 1244433440#u32 877405136#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (397140113 < 2147483647 ∧ 986979750 < 2147483647) ∧ (1638334236 < 2147483647 ∧ 1167960466 < 2147483647); omega) canonical10 (by rfl)
#print axioms add10
theorem mul09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1456048369#u32 1529875538#u32 1244433440#u32 877405136#u32) (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32)=ok (q 2085151610#u32 860319931#u32 1669909752#u32 1768068034#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1456048369 < 2147483647 ∧ 1529875538 < 2147483647) ∧ (1244433440 < 2147483647 ∧ 877405136 < 2147483647); omega) (by change (528783666 < 2147483647 ∧ 1672539309 < 2147483647) ∧ (1274387717 < 2147483647 ∧ 552414171 < 2147483647); omega) (by rfl)
#print axioms mul09
theorem add09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2085151610#u32 860319931#u32 1669909752#u32 1768068034#u32) c09=ok (q 2080096119#u32 1071336586#u32 584975793#u32 868767185#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2085151610 < 2147483647 ∧ 860319931 < 2147483647) ∧ (1669909752 < 2147483647 ∧ 1768068034 < 2147483647); omega) canonical09 (by rfl)
#print axioms add09
theorem mul08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2080096119#u32 1071336586#u32 584975793#u32 868767185#u32) (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32)=ok (q 1421476491#u32 550278917#u32 1346563883#u32 1423269336#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2080096119 < 2147483647 ∧ 1071336586 < 2147483647) ∧ (584975793 < 2147483647 ∧ 868767185 < 2147483647); omega) (by change (528783666 < 2147483647 ∧ 1672539309 < 2147483647) ∧ (1274387717 < 2147483647 ∧ 552414171 < 2147483647); omega) (by rfl)
#print axioms mul08
theorem add08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1421476491#u32 550278917#u32 1346563883#u32 1423269336#u32) c08=ok (q 880640374#u32 2011679603#u32 1767445701#u32 1056808858#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1421476491 < 2147483647 ∧ 550278917 < 2147483647) ∧ (1346563883 < 2147483647 ∧ 1423269336 < 2147483647); omega) canonical08 (by rfl)
#print axioms add08
theorem mul07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 880640374#u32 2011679603#u32 1767445701#u32 1056808858#u32) (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32)=ok (q 187877380#u32 2069920951#u32 1560616706#u32 1275766537#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (880640374 < 2147483647 ∧ 2011679603 < 2147483647) ∧ (1767445701 < 2147483647 ∧ 1056808858 < 2147483647); omega) (by change (528783666 < 2147483647 ∧ 1672539309 < 2147483647) ∧ (1274387717 < 2147483647 ∧ 552414171 < 2147483647); omega) (by rfl)
#print axioms mul07
theorem add07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 187877380#u32 2069920951#u32 1560616706#u32 1275766537#u32) c07=ok (q 1842499371#u32 1896329910#u32 1589895043#u32 685913453#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (187877380 < 2147483647 ∧ 2069920951 < 2147483647) ∧ (1560616706 < 2147483647 ∧ 1275766537 < 2147483647); omega) canonical07 (by rfl)
#print axioms add07
theorem mul06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1842499371#u32 1896329910#u32 1589895043#u32 685913453#u32) (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32)=ok (q 1831433963#u32 1892911644#u32 211980456#u32 1223788455#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1842499371 < 2147483647 ∧ 1896329910 < 2147483647) ∧ (1589895043 < 2147483647 ∧ 685913453 < 2147483647); omega) (by change (528783666 < 2147483647 ∧ 1672539309 < 2147483647) ∧ (1274387717 < 2147483647 ∧ 552414171 < 2147483647); omega) (by rfl)
#print axioms mul06
theorem add06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1831433963#u32 1892911644#u32 211980456#u32 1223788455#u32) c06=ok (q 1585938543#u32 1663929716#u32 1367024917#u32 872538994#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1831433963 < 2147483647 ∧ 1892911644 < 2147483647) ∧ (211980456 < 2147483647 ∧ 1223788455 < 2147483647); omega) canonical06 (by rfl)
#print axioms add06
theorem mul05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1585938543#u32 1663929716#u32 1367024917#u32 872538994#u32) (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32)=ok (q 97527544#u32 1432250185#u32 1315019187#u32 1413849023#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1585938543 < 2147483647 ∧ 1663929716 < 2147483647) ∧ (1367024917 < 2147483647 ∧ 872538994 < 2147483647); omega) (by change (528783666 < 2147483647 ∧ 1672539309 < 2147483647) ∧ (1274387717 < 2147483647 ∧ 552414171 < 2147483647); omega) (by rfl)
#print axioms mul05
theorem add05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 97527544#u32 1432250185#u32 1315019187#u32 1413849023#u32) c05=ok (q 113949408#u32 736259754#u32 1287756738#u32 621770806#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (97527544 < 2147483647 ∧ 1432250185 < 2147483647) ∧ (1315019187 < 2147483647 ∧ 1413849023 < 2147483647); omega) canonical05 (by rfl)
#print axioms add05
theorem mul04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 113949408#u32 736259754#u32 1287756738#u32 621770806#u32) (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32)=ok (q 531282023#u32 1587543281#u32 1133789882#u32 644015134#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (113949408 < 2147483647 ∧ 736259754 < 2147483647) ∧ (1287756738 < 2147483647 ∧ 621770806 < 2147483647); omega) (by change (528783666 < 2147483647 ∧ 1672539309 < 2147483647) ∧ (1274387717 < 2147483647 ∧ 552414171 < 2147483647); omega) (by rfl)
#print axioms mul04
theorem add04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 531282023#u32 1587543281#u32 1133789882#u32 644015134#u32) c04=ok (q 188136180#u32 1917171759#u32 785999378#u32 2106199051#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (531282023 < 2147483647 ∧ 1587543281 < 2147483647) ∧ (1133789882 < 2147483647 ∧ 644015134 < 2147483647); omega) canonical04 (by rfl)
#print axioms add04
theorem mul03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 188136180#u32 1917171759#u32 785999378#u32 2106199051#u32) (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32)=ok (q 1382178005#u32 1577974946#u32 703958818#u32 884591988#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (188136180 < 2147483647 ∧ 1917171759 < 2147483647) ∧ (785999378 < 2147483647 ∧ 2106199051 < 2147483647); omega) (by change (528783666 < 2147483647 ∧ 1672539309 < 2147483647) ∧ (1274387717 < 2147483647 ∧ 552414171 < 2147483647); omega) (by rfl)
#print axioms mul03
theorem add03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1382178005#u32 1577974946#u32 703958818#u32 884591988#u32) c03=ok (q 363795853#u32 226101701#u32 1881792794#u32 2041465790#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1382178005 < 2147483647 ∧ 1577974946 < 2147483647) ∧ (703958818 < 2147483647 ∧ 884591988 < 2147483647); omega) canonical03 (by rfl)
#print axioms add03
theorem mul02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 363795853#u32 226101701#u32 1881792794#u32 2041465790#u32) (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32)=ok (q 936508656#u32 667560144#u32 21670387#u32 1857393098#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (363795853 < 2147483647 ∧ 226101701 < 2147483647) ∧ (1881792794 < 2147483647 ∧ 2041465790 < 2147483647); omega) (by change (528783666 < 2147483647 ∧ 1672539309 < 2147483647) ∧ (1274387717 < 2147483647 ∧ 552414171 < 2147483647); omega) (by rfl)
#print axioms mul02
theorem add02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 936508656#u32 667560144#u32 21670387#u32 1857393098#u32) c02=ok (q 1415922186#u32 1335017475#u32 1881579875#u32 818439052#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (936508656 < 2147483647 ∧ 667560144 < 2147483647) ∧ (21670387 < 2147483647 ∧ 1857393098 < 2147483647); omega) canonical02 (by rfl)
#print axioms add02
theorem mul01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1415922186#u32 1335017475#u32 1881579875#u32 818439052#u32) (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32)=ok (q 1289480884#u32 1045337421#u32 55723733#u32 679905597#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1415922186 < 2147483647 ∧ 1335017475 < 2147483647) ∧ (1881579875 < 2147483647 ∧ 818439052 < 2147483647); omega) (by change (528783666 < 2147483647 ∧ 1672539309 < 2147483647) ∧ (1274387717 < 2147483647 ∧ 552414171 < 2147483647); omega) (by rfl)
#print axioms mul01
theorem add01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1289480884#u32 1045337421#u32 55723733#u32 679905597#u32) c01=ok (q 675099258#u32 2054225428#u32 42605328#u32 837652419#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1289480884 < 2147483647 ∧ 1045337421 < 2147483647) ∧ (55723733 < 2147483647 ∧ 679905597 < 2147483647); omega) canonical01 (by rfl)
#print axioms add01
theorem mul00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 675099258#u32 2054225428#u32 42605328#u32 837652419#u32) (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32)=ok (q 314771277#u32 692567940#u32 779177182#u32 291448782#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (675099258 < 2147483647 ∧ 2054225428 < 2147483647) ∧ (42605328 < 2147483647 ∧ 837652419 < 2147483647); omega) (by change (528783666 < 2147483647 ∧ 1672539309 < 2147483647) ∧ (1274387717 < 2147483647 ∧ 552414171 < 2147483647); omega) (by rfl)
#print axioms mul00
theorem add00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 314771277#u32 692567940#u32 779177182#u32 291448782#u32) c00=ok (q 551881536#u32 1775538161#u32 358117935#u32 1029669789#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (314771277 < 2147483647 ∧ 692567940 < 2147483647) ∧ (779177182 < 2147483647 ∧ 291448782 < 2147483647); omega) canonical00 (by rfl)
#print axioms add00
def final : Q := (q 551881536#u32 1775538161#u32 358117935#u32 1029669789#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 1#usize 14#usize initial 0#usize final := by
  refine .step (by change 14>0; omega) (JFr_IndexArithmetic.sub 14#usize 13#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32) from rfl) mul13 (show Array.index_usize p 13#usize=ok c13 from rfl) add13 ?_
  refine .step (by change 13>0; omega) (JFr_IndexArithmetic.sub 13#usize 12#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32) from rfl) mul12 (show Array.index_usize p 12#usize=ok c12 from rfl) add12 ?_
  refine .step (by change 12>0; omega) (JFr_IndexArithmetic.sub 12#usize 11#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32) from rfl) mul11 (show Array.index_usize p 11#usize=ok c11 from rfl) add11 ?_
  refine .step (by change 11>0; omega) (JFr_IndexArithmetic.sub 11#usize 10#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32) from rfl) mul10 (show Array.index_usize p 10#usize=ok c10 from rfl) add10 ?_
  refine .step (by change 10>0; omega) (JFr_IndexArithmetic.sub 10#usize 9#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32) from rfl) mul09 (show Array.index_usize p 9#usize=ok c09 from rfl) add09 ?_
  refine .step (by change 9>0; omega) (JFr_IndexArithmetic.sub 9#usize 8#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32) from rfl) mul08 (show Array.index_usize p 8#usize=ok c08 from rfl) add08 ?_
  refine .step (by change 8>0; omega) (JFr_IndexArithmetic.sub 8#usize 7#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32) from rfl) mul07 (show Array.index_usize p 7#usize=ok c07 from rfl) add07 ?_
  refine .step (by change 7>0; omega) (JFr_IndexArithmetic.sub 7#usize 6#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32) from rfl) mul06 (show Array.index_usize p 6#usize=ok c06 from rfl) add06 ?_
  refine .step (by change 6>0; omega) (JFr_IndexArithmetic.sub 6#usize 5#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32) from rfl) mul05 (show Array.index_usize p 5#usize=ok c05 from rfl) add05 ?_
  refine .step (by change 5>0; omega) (JFr_IndexArithmetic.sub 5#usize 4#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32) from rfl) mul04 (show Array.index_usize p 4#usize=ok c04 from rfl) add04 ?_
  refine .step (by change 4>0; omega) (JFr_IndexArithmetic.sub 4#usize 3#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32) from rfl) mul03 (show Array.index_usize p 3#usize=ok c03 from rfl) add03 ?_
  refine .step (by change 3>0; omega) (JFr_IndexArithmetic.sub 3#usize 2#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32) from rfl) mul02 (show Array.index_usize p 2#usize=ok c02 from rfl) add02 ?_
  refine .step (by change 2>0; omega) (JFr_IndexArithmetic.sub 2#usize 1#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32) from rfl) mul01 (show Array.index_usize p 1#usize=ok c01 from rfl) add01 ?_
  refine .step (by change 1>0; omega) (JFr_IndexArithmetic.sub 1#usize 0#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32) from rfl) mul00 (show Array.index_usize p 0#usize=ok c00 from rfl) add00 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner01_1
