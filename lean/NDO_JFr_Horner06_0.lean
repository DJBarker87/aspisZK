import NDO_JFr_Data06
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner06_0
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data06
def initial : Q := (q 0#u32 0#u32 0#u32 0#u32)
theorem mul27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 0#u32 0#u32 0#u32 0#u32) (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32)=ok (q 0#u32 0#u32 0#u32 0#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) (by change (1410683225 < 2147483647 ∧ 375596669 < 2147483647) ∧ (973261870 < 2147483647 ∧ 122086709 < 2147483647); omega) (by rfl)
#print axioms mul27
theorem add27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 0#u32 0#u32 0#u32 0#u32) c27=ok (q 682926273#u32 1914189830#u32 1607002815#u32 582840931#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) canonical27 (by rfl)
#print axioms add27
theorem mul26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 682926273#u32 1914189830#u32 1607002815#u32 582840931#u32) (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32)=ok (q 701385431#u32 1120976833#u32 891339709#u32 1620611510#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (682926273 < 2147483647 ∧ 1914189830 < 2147483647) ∧ (1607002815 < 2147483647 ∧ 582840931 < 2147483647); omega) (by change (1410683225 < 2147483647 ∧ 375596669 < 2147483647) ∧ (973261870 < 2147483647 ∧ 122086709 < 2147483647); omega) (by rfl)
#print axioms mul26
theorem add26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 701385431#u32 1120976833#u32 891339709#u32 1620611510#u32) c26=ok (q 1942707356#u32 346407198#u32 358733038#u32 1066839637#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (701385431 < 2147483647 ∧ 1120976833 < 2147483647) ∧ (891339709 < 2147483647 ∧ 1620611510 < 2147483647); omega) canonical26 (by rfl)
#print axioms add26
theorem mul25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1942707356#u32 346407198#u32 358733038#u32 1066839637#u32) (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32)=ok (q 1043032811#u32 724552880#u32 1192919930#u32 216320856#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1942707356 < 2147483647 ∧ 346407198 < 2147483647) ∧ (358733038 < 2147483647 ∧ 1066839637 < 2147483647); omega) (by change (1410683225 < 2147483647 ∧ 375596669 < 2147483647) ∧ (973261870 < 2147483647 ∧ 122086709 < 2147483647); omega) (by rfl)
#print axioms mul25
theorem add25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1043032811#u32 724552880#u32 1192919930#u32 216320856#u32) c25=ok (q 1342317942#u32 1911750961#u32 1434437435#u32 482961495#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1043032811 < 2147483647 ∧ 724552880 < 2147483647) ∧ (1192919930 < 2147483647 ∧ 216320856 < 2147483647); omega) canonical25 (by rfl)
#print axioms add25
theorem mul24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1342317942#u32 1911750961#u32 1434437435#u32 482961495#u32) (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32)=ok (q 492323864#u32 2045076445#u32 1612660838#u32 892967546#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1342317942 < 2147483647 ∧ 1911750961 < 2147483647) ∧ (1434437435 < 2147483647 ∧ 482961495 < 2147483647); omega) (by change (1410683225 < 2147483647 ∧ 375596669 < 2147483647) ∧ (973261870 < 2147483647 ∧ 122086709 < 2147483647); omega) (by rfl)
#print axioms mul24
theorem add24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 492323864#u32 2045076445#u32 1612660838#u32 892967546#u32) c24=ok (q 920925519#u32 1111416854#u32 1631092097#u32 311550129#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (492323864 < 2147483647 ∧ 2045076445 < 2147483647) ∧ (1612660838 < 2147483647 ∧ 892967546 < 2147483647); omega) canonical24 (by rfl)
#print axioms add24
theorem mul23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 920925519#u32 1111416854#u32 1631092097#u32 311550129#u32) (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32)=ok (q 1896238335#u32 248453650#u32 2101294199#u32 1398322872#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (920925519 < 2147483647 ∧ 1111416854 < 2147483647) ∧ (1631092097 < 2147483647 ∧ 311550129 < 2147483647); omega) (by change (1410683225 < 2147483647 ∧ 375596669 < 2147483647) ∧ (973261870 < 2147483647 ∧ 122086709 < 2147483647); omega) (by rfl)
#print axioms mul23
theorem add23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1896238335#u32 248453650#u32 2101294199#u32 1398322872#u32) c23=ok (q 622204148#u32 1110126873#u32 1930749901#u32 1893353897#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1896238335 < 2147483647 ∧ 248453650 < 2147483647) ∧ (2101294199 < 2147483647 ∧ 1398322872 < 2147483647); omega) canonical23 (by rfl)
#print axioms add23
theorem mul22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 622204148#u32 1110126873#u32 1930749901#u32 1893353897#u32) (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32)=ok (q 1232110493#u32 413697515#u32 1800721378#u32 141334388#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (622204148 < 2147483647 ∧ 1110126873 < 2147483647) ∧ (1930749901 < 2147483647 ∧ 1893353897 < 2147483647); omega) (by change (1410683225 < 2147483647 ∧ 375596669 < 2147483647) ∧ (973261870 < 2147483647 ∧ 122086709 < 2147483647); omega) (by rfl)
#print axioms mul22
theorem add22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1232110493#u32 413697515#u32 1800721378#u32 141334388#u32) c22=ok (q 311685935#u32 346838419#u32 1909907335#u32 2060853851#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1232110493 < 2147483647 ∧ 413697515 < 2147483647) ∧ (1800721378 < 2147483647 ∧ 141334388 < 2147483647); omega) canonical22 (by rfl)
#print axioms add22
theorem mul21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 311685935#u32 346838419#u32 1909907335#u32 2060853851#u32) (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32)=ok (q 2130168241#u32 1442195873#u32 2105715337#u32 359651381#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (311685935 < 2147483647 ∧ 346838419 < 2147483647) ∧ (1909907335 < 2147483647 ∧ 2060853851 < 2147483647); omega) (by change (1410683225 < 2147483647 ∧ 375596669 < 2147483647) ∧ (973261870 < 2147483647 ∧ 122086709 < 2147483647); omega) (by rfl)
#print axioms mul21
theorem add21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2130168241#u32 1442195873#u32 2105715337#u32 359651381#u32) c21=ok (q 185857330#u32 1894916254#u32 122415000#u32 1521764259#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2130168241 < 2147483647 ∧ 1442195873 < 2147483647) ∧ (2105715337 < 2147483647 ∧ 359651381 < 2147483647); omega) canonical21 (by rfl)
#print axioms add21
theorem mul20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 185857330#u32 1894916254#u32 122415000#u32 1521764259#u32) (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32)=ok (q 1062999925#u32 588240511#u32 181634104#u32 779872118#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (185857330 < 2147483647 ∧ 1894916254 < 2147483647) ∧ (122415000 < 2147483647 ∧ 1521764259 < 2147483647); omega) (by change (1410683225 < 2147483647 ∧ 375596669 < 2147483647) ∧ (973261870 < 2147483647 ∧ 122086709 < 2147483647); omega) (by rfl)
#print axioms mul20
theorem add20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1062999925#u32 588240511#u32 181634104#u32 779872118#u32) c20=ok (q 1477298175#u32 1476499344#u32 1960790321#u32 1426234375#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1062999925 < 2147483647 ∧ 588240511 < 2147483647) ∧ (181634104 < 2147483647 ∧ 779872118 < 2147483647); omega) canonical20 (by rfl)
#print axioms add20
theorem mul19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1477298175#u32 1476499344#u32 1960790321#u32 1426234375#u32) (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32)=ok (q 1748617838#u32 482432839#u32 84391352#u32 1216932232#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1477298175 < 2147483647 ∧ 1476499344 < 2147483647) ∧ (1960790321 < 2147483647 ∧ 1426234375 < 2147483647); omega) (by change (1410683225 < 2147483647 ∧ 375596669 < 2147483647) ∧ (973261870 < 2147483647 ∧ 122086709 < 2147483647); omega) (by rfl)
#print axioms mul19
theorem add19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1748617838#u32 482432839#u32 84391352#u32 1216932232#u32) c19=ok (q 883274235#u32 393495719#u32 1233825606#u32 383482273#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1748617838 < 2147483647 ∧ 482432839 < 2147483647) ∧ (84391352 < 2147483647 ∧ 1216932232 < 2147483647); omega) canonical19 (by rfl)
#print axioms add19
theorem mul18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 883274235#u32 393495719#u32 1233825606#u32 383482273#u32) (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32)=ok (q 1349893354#u32 1062852570#u32 3139614#u32 156830705#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (883274235 < 2147483647 ∧ 393495719 < 2147483647) ∧ (1233825606 < 2147483647 ∧ 383482273 < 2147483647); omega) (by change (1410683225 < 2147483647 ∧ 375596669 < 2147483647) ∧ (973261870 < 2147483647 ∧ 122086709 < 2147483647); omega) (by rfl)
#print axioms mul18
theorem add18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1349893354#u32 1062852570#u32 3139614#u32 156830705#u32) c18=ok (q 1251367917#u32 1134863618#u32 721240128#u32 1586673646#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1349893354 < 2147483647 ∧ 1062852570 < 2147483647) ∧ (3139614 < 2147483647 ∧ 156830705 < 2147483647); omega) canonical18 (by rfl)
#print axioms add18
theorem mul17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1251367917#u32 1134863618#u32 721240128#u32 1586673646#u32) (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32)=ok (q 997571001#u32 254003573#u32 623840386#u32 2054676787#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1251367917 < 2147483647 ∧ 1134863618 < 2147483647) ∧ (721240128 < 2147483647 ∧ 1586673646 < 2147483647); omega) (by change (1410683225 < 2147483647 ∧ 375596669 < 2147483647) ∧ (973261870 < 2147483647 ∧ 122086709 < 2147483647); omega) (by rfl)
#print axioms mul17
theorem add17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 997571001#u32 254003573#u32 623840386#u32 2054676787#u32) c17=ok (q 1216759437#u32 469443471#u32 1279100780#u32 1423736474#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (997571001 < 2147483647 ∧ 254003573 < 2147483647) ∧ (623840386 < 2147483647 ∧ 2054676787 < 2147483647); omega) canonical17 (by rfl)
#print axioms add17
theorem mul16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1216759437#u32 469443471#u32 1279100780#u32 1423736474#u32) (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32)=ok (q 440747023#u32 1061655102#u32 1596389644#u32 590306296#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1216759437 < 2147483647 ∧ 469443471 < 2147483647) ∧ (1279100780 < 2147483647 ∧ 1423736474 < 2147483647); omega) (by change (1410683225 < 2147483647 ∧ 375596669 < 2147483647) ∧ (973261870 < 2147483647 ∧ 122086709 < 2147483647); omega) (by rfl)
#print axioms mul16
theorem add16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 440747023#u32 1061655102#u32 1596389644#u32 590306296#u32) c16=ok (q 1225317848#u32 1939390894#u32 1441727473#u32 1424758408#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (440747023 < 2147483647 ∧ 1061655102 < 2147483647) ∧ (1596389644 < 2147483647 ∧ 590306296 < 2147483647); omega) canonical16 (by rfl)
#print axioms add16
theorem mul15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1225317848#u32 1939390894#u32 1441727473#u32 1424758408#u32) (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32)=ok (q 589645200#u32 1433972449#u32 1386264476#u32 1806930462#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1225317848 < 2147483647 ∧ 1939390894 < 2147483647) ∧ (1441727473 < 2147483647 ∧ 1424758408 < 2147483647); omega) (by change (1410683225 < 2147483647 ∧ 375596669 < 2147483647) ∧ (973261870 < 2147483647 ∧ 122086709 < 2147483647); omega) (by rfl)
#print axioms mul15
theorem add15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 589645200#u32 1433972449#u32 1386264476#u32 1806930462#u32) c15=ok (q 2146760756#u32 195346823#u32 1435537716#u32 840472471#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (589645200 < 2147483647 ∧ 1433972449 < 2147483647) ∧ (1386264476 < 2147483647 ∧ 1806930462 < 2147483647); omega) canonical15 (by rfl)
#print axioms add15
theorem mul14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2146760756#u32 195346823#u32 1435537716#u32 840472471#u32) (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32)=ok (q 1118697887#u32 2017060799#u32 795419613#u32 728376134#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2146760756 < 2147483647 ∧ 195346823 < 2147483647) ∧ (1435537716 < 2147483647 ∧ 840472471 < 2147483647); omega) (by change (1410683225 < 2147483647 ∧ 375596669 < 2147483647) ∧ (973261870 < 2147483647 ∧ 122086709 < 2147483647); omega) (by rfl)
#print axioms mul14
theorem add14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1118697887#u32 2017060799#u32 795419613#u32 728376134#u32) c14=ok (q 1321604998#u32 468043454#u32 1940954367#u32 1303357150#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1118697887 < 2147483647 ∧ 2017060799 < 2147483647) ∧ (795419613 < 2147483647 ∧ 728376134 < 2147483647); omega) canonical14 (by rfl)
#print axioms add14
def final : Q := (q 1321604998#u32 468043454#u32 1940954367#u32 1303357150#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 6#usize 28#usize initial 14#usize final := by
  refine .step (by change 28>0; omega) (JFr_IndexArithmetic.sub 28#usize 27#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32) from rfl) mul27 (show Array.index_usize p 27#usize=ok c27 from rfl) add27 ?_
  refine .step (by change 27>0; omega) (JFr_IndexArithmetic.sub 27#usize 26#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32) from rfl) mul26 (show Array.index_usize p 26#usize=ok c26 from rfl) add26 ?_
  refine .step (by change 26>0; omega) (JFr_IndexArithmetic.sub 26#usize 25#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32) from rfl) mul25 (show Array.index_usize p 25#usize=ok c25 from rfl) add25 ?_
  refine .step (by change 25>0; omega) (JFr_IndexArithmetic.sub 25#usize 24#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32) from rfl) mul24 (show Array.index_usize p 24#usize=ok c24 from rfl) add24 ?_
  refine .step (by change 24>0; omega) (JFr_IndexArithmetic.sub 24#usize 23#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32) from rfl) mul23 (show Array.index_usize p 23#usize=ok c23 from rfl) add23 ?_
  refine .step (by change 23>0; omega) (JFr_IndexArithmetic.sub 23#usize 22#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32) from rfl) mul22 (show Array.index_usize p 22#usize=ok c22 from rfl) add22 ?_
  refine .step (by change 22>0; omega) (JFr_IndexArithmetic.sub 22#usize 21#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32) from rfl) mul21 (show Array.index_usize p 21#usize=ok c21 from rfl) add21 ?_
  refine .step (by change 21>0; omega) (JFr_IndexArithmetic.sub 21#usize 20#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32) from rfl) mul20 (show Array.index_usize p 20#usize=ok c20 from rfl) add20 ?_
  refine .step (by change 20>0; omega) (JFr_IndexArithmetic.sub 20#usize 19#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32) from rfl) mul19 (show Array.index_usize p 19#usize=ok c19 from rfl) add19 ?_
  refine .step (by change 19>0; omega) (JFr_IndexArithmetic.sub 19#usize 18#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32) from rfl) mul18 (show Array.index_usize p 18#usize=ok c18 from rfl) add18 ?_
  refine .step (by change 18>0; omega) (JFr_IndexArithmetic.sub 18#usize 17#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32) from rfl) mul17 (show Array.index_usize p 17#usize=ok c17 from rfl) add17 ?_
  refine .step (by change 17>0; omega) (JFr_IndexArithmetic.sub 17#usize 16#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32) from rfl) mul16 (show Array.index_usize p 16#usize=ok c16 from rfl) add16 ?_
  refine .step (by change 16>0; omega) (JFr_IndexArithmetic.sub 16#usize 15#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32) from rfl) mul15 (show Array.index_usize p 15#usize=ok c15 from rfl) add15 ?_
  refine .step (by change 15>0; omega) (JFr_IndexArithmetic.sub 15#usize 14#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32) from rfl) mul14 (show Array.index_usize p 14#usize=ok c14 from rfl) add14 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner06_0
