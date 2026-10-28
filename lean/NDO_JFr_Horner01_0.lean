import NDO_JFr_Data01
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner01_0
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data01
def initial : Q := (q 0#u32 0#u32 0#u32 0#u32)
theorem mul27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 0#u32 0#u32 0#u32 0#u32) (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32)=ok (q 0#u32 0#u32 0#u32 0#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) (by change (528783666 < 2147483647 ∧ 1672539309 < 2147483647) ∧ (1274387717 < 2147483647 ∧ 552414171 < 2147483647); omega) (by rfl)
#print axioms mul27
theorem add27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 0#u32 0#u32 0#u32 0#u32) c27=ok (q 892814474#u32 239899553#u32 740593163#u32 12847331#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) canonical27 (by rfl)
#print axioms add27
theorem mul26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 892814474#u32 239899553#u32 740593163#u32 12847331#u32) (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32)=ok (q 498476755#u32 1105314796#u32 536441200#u32 1061437762#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (892814474 < 2147483647 ∧ 239899553 < 2147483647) ∧ (740593163 < 2147483647 ∧ 12847331 < 2147483647); omega) (by change (528783666 < 2147483647 ∧ 1672539309 < 2147483647) ∧ (1274387717 < 2147483647 ∧ 552414171 < 2147483647); omega) (by rfl)
#print axioms mul26
theorem add26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 498476755#u32 1105314796#u32 536441200#u32 1061437762#u32) c26=ok (q 2033656905#u32 315832369#u32 634021308#u32 965776155#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (498476755 < 2147483647 ∧ 1105314796 < 2147483647) ∧ (536441200 < 2147483647 ∧ 1061437762 < 2147483647); omega) canonical26 (by rfl)
#print axioms add26
theorem mul25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2033656905#u32 315832369#u32 634021308#u32 965776155#u32) (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32)=ok (q 184791210#u32 883018927#u32 11016828#u32 372118325#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2033656905 < 2147483647 ∧ 315832369 < 2147483647) ∧ (634021308 < 2147483647 ∧ 965776155 < 2147483647); omega) (by change (528783666 < 2147483647 ∧ 1672539309 < 2147483647) ∧ (1274387717 < 2147483647 ∧ 552414171 < 2147483647); omega) (by rfl)
#print axioms mul25
theorem add25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 184791210#u32 883018927#u32 11016828#u32 372118325#u32) c25=ok (q 119926608#u32 1581382222#u32 544990370#u32 2096259008#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (184791210 < 2147483647 ∧ 883018927 < 2147483647) ∧ (11016828 < 2147483647 ∧ 372118325 < 2147483647); omega) canonical25 (by rfl)
#print axioms add25
theorem mul24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 119926608#u32 1581382222#u32 544990370#u32 2096259008#u32) (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32)=ok (q 2068078162#u32 1854144569#u32 828215540#u32 292441334#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (119926608 < 2147483647 ∧ 1581382222 < 2147483647) ∧ (544990370 < 2147483647 ∧ 2096259008 < 2147483647); omega) (by change (528783666 < 2147483647 ∧ 1672539309 < 2147483647) ∧ (1274387717 < 2147483647 ∧ 552414171 < 2147483647); omega) (by rfl)
#print axioms mul24
theorem add24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2068078162#u32 1854144569#u32 828215540#u32 292441334#u32) c24=ok (q 701496043#u32 40384754#u32 527243906#u32 1194954689#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2068078162 < 2147483647 ∧ 1854144569 < 2147483647) ∧ (828215540 < 2147483647 ∧ 292441334 < 2147483647); omega) canonical24 (by rfl)
#print axioms add24
theorem mul23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 701496043#u32 40384754#u32 527243906#u32 1194954689#u32) (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32)=ok (q 981825929#u32 516504920#u32 1352535401#u32 295274831#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (701496043 < 2147483647 ∧ 40384754 < 2147483647) ∧ (527243906 < 2147483647 ∧ 1194954689 < 2147483647); omega) (by change (528783666 < 2147483647 ∧ 1672539309 < 2147483647) ∧ (1274387717 < 2147483647 ∧ 552414171 < 2147483647); omega) (by rfl)
#print axioms mul23
theorem add23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 981825929#u32 516504920#u32 1352535401#u32 295274831#u32) c23=ok (q 994152256#u32 1592666671#u32 239411684#u32 2119527740#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (981825929 < 2147483647 ∧ 516504920 < 2147483647) ∧ (1352535401 < 2147483647 ∧ 295274831 < 2147483647); omega) canonical23 (by rfl)
#print axioms add23
theorem mul22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 994152256#u32 1592666671#u32 239411684#u32 2119527740#u32) (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32)=ok (q 1274390102#u32 141820564#u32 2139903263#u32 2102452328#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (994152256 < 2147483647 ∧ 1592666671 < 2147483647) ∧ (239411684 < 2147483647 ∧ 2119527740 < 2147483647); omega) (by change (528783666 < 2147483647 ∧ 1672539309 < 2147483647) ∧ (1274387717 < 2147483647 ∧ 552414171 < 2147483647); omega) (by rfl)
#print axioms mul22
theorem add22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1274390102#u32 141820564#u32 2139903263#u32 2102452328#u32) c22=ok (q 649729988#u32 1132336443#u32 2044980223#u32 388181312#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1274390102 < 2147483647 ∧ 141820564 < 2147483647) ∧ (2139903263 < 2147483647 ∧ 2102452328 < 2147483647); omega) canonical22 (by rfl)
#print axioms add22
theorem mul21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 649729988#u32 1132336443#u32 2044980223#u32 388181312#u32) (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32)=ok (q 1964726601#u32 1720238975#u32 1458147478#u32 839608887#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (649729988 < 2147483647 ∧ 1132336443 < 2147483647) ∧ (2044980223 < 2147483647 ∧ 388181312 < 2147483647); omega) (by change (528783666 < 2147483647 ∧ 1672539309 < 2147483647) ∧ (1274387717 < 2147483647 ∧ 552414171 < 2147483647); omega) (by rfl)
#print axioms mul21
theorem add21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1964726601#u32 1720238975#u32 1458147478#u32 839608887#u32) c21=ok (q 659368229#u32 1380285636#u32 511178046#u32 1450601512#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1964726601 < 2147483647 ∧ 1720238975 < 2147483647) ∧ (1458147478 < 2147483647 ∧ 839608887 < 2147483647); omega) canonical21 (by rfl)
#print axioms add21
theorem mul20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 659368229#u32 1380285636#u32 511178046#u32 1450601512#u32) (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32)=ok (q 1395229408#u32 1016082312#u32 861546319#u32 1220464282#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (659368229 < 2147483647 ∧ 1380285636 < 2147483647) ∧ (511178046 < 2147483647 ∧ 1450601512 < 2147483647); omega) (by change (528783666 < 2147483647 ∧ 1672539309 < 2147483647) ∧ (1274387717 < 2147483647 ∧ 552414171 < 2147483647); omega) (by rfl)
#print axioms mul20
theorem add20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1395229408#u32 1016082312#u32 861546319#u32 1220464282#u32) c20=ok (q 1586770268#u32 1050365498#u32 1812592259#u32 1001274533#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1395229408 < 2147483647 ∧ 1016082312 < 2147483647) ∧ (861546319 < 2147483647 ∧ 1220464282 < 2147483647); omega) canonical20 (by rfl)
#print axioms add20
theorem mul19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1586770268#u32 1050365498#u32 1812592259#u32 1001274533#u32) (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32)=ok (q 1049827013#u32 374511576#u32 1097114301#u32 1383732109#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1586770268 < 2147483647 ∧ 1050365498 < 2147483647) ∧ (1812592259 < 2147483647 ∧ 1001274533 < 2147483647); omega) (by change (528783666 < 2147483647 ∧ 1672539309 < 2147483647) ∧ (1274387717 < 2147483647 ∧ 552414171 < 2147483647); omega) (by rfl)
#print axioms mul19
theorem add19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1049827013#u32 374511576#u32 1097114301#u32 1383732109#u32) c19=ok (q 1264722415#u32 1936651447#u32 1699465456#u32 2072257108#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1049827013 < 2147483647 ∧ 374511576 < 2147483647) ∧ (1097114301 < 2147483647 ∧ 1383732109 < 2147483647); omega) canonical19 (by rfl)
#print axioms add19
theorem mul18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1264722415#u32 1936651447#u32 1699465456#u32 2072257108#u32) (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32)=ok (q 455307844#u32 701328261#u32 2143360684#u32 1670738004#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1264722415 < 2147483647 ∧ 1936651447 < 2147483647) ∧ (1699465456 < 2147483647 ∧ 2072257108 < 2147483647); omega) (by change (528783666 < 2147483647 ∧ 1672539309 < 2147483647) ∧ (1274387717 < 2147483647 ∧ 552414171 < 2147483647); omega) (by rfl)
#print axioms mul18
theorem add18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 455307844#u32 701328261#u32 2143360684#u32 1670738004#u32) c18=ok (q 1723931193#u32 131067036#u32 896014081#u32 100230205#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (455307844 < 2147483647 ∧ 701328261 < 2147483647) ∧ (2143360684 < 2147483647 ∧ 1670738004 < 2147483647); omega) canonical18 (by rfl)
#print axioms add18
theorem mul17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1723931193#u32 131067036#u32 896014081#u32 100230205#u32) (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32)=ok (q 1098286844#u32 2005744775#u32 42743857#u32 1648768302#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1723931193 < 2147483647 ∧ 131067036 < 2147483647) ∧ (896014081 < 2147483647 ∧ 100230205 < 2147483647); omega) (by change (528783666 < 2147483647 ∧ 1672539309 < 2147483647) ∧ (1274387717 < 2147483647 ∧ 552414171 < 2147483647); omega) (by rfl)
#print axioms mul17
theorem add17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1098286844#u32 2005744775#u32 42743857#u32 1648768302#u32) c17=ok (q 83606957#u32 842224835#u32 487579212#u32 1007059159#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1098286844 < 2147483647 ∧ 2005744775 < 2147483647) ∧ (42743857 < 2147483647 ∧ 1648768302 < 2147483647); omega) canonical17 (by rfl)
#print axioms add17
theorem mul16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 83606957#u32 842224835#u32 487579212#u32 1007059159#u32) (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32)=ok (q 428867300#u32 970906118#u32 1253983790#u32 1350650146#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (83606957 < 2147483647 ∧ 842224835 < 2147483647) ∧ (487579212 < 2147483647 ∧ 1007059159 < 2147483647); omega) (by change (528783666 < 2147483647 ∧ 1672539309 < 2147483647) ∧ (1274387717 < 2147483647 ∧ 552414171 < 2147483647); omega) (by rfl)
#print axioms mul16
theorem add16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 428867300#u32 970906118#u32 1253983790#u32 1350650146#u32) c16=ok (q 395255752#u32 277646157#u32 1231778555#u32 791961467#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (428867300 < 2147483647 ∧ 970906118 < 2147483647) ∧ (1253983790 < 2147483647 ∧ 1350650146 < 2147483647); omega) canonical16 (by rfl)
#print axioms add16
theorem mul15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 395255752#u32 277646157#u32 1231778555#u32 791961467#u32) (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32)=ok (q 1156668515#u32 1014800006#u32 888623889#u32 1163898945#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (395255752 < 2147483647 ∧ 277646157 < 2147483647) ∧ (1231778555 < 2147483647 ∧ 791961467 < 2147483647); omega) (by change (528783666 < 2147483647 ∧ 1672539309 < 2147483647) ∧ (1274387717 < 2147483647 ∧ 552414171 < 2147483647); omega) (by rfl)
#print axioms mul15
theorem add15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1156668515#u32 1014800006#u32 888623889#u32 1163898945#u32) c15=ok (q 1599780737#u32 2105233088#u32 1384773872#u32 177371747#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1156668515 < 2147483647 ∧ 1014800006 < 2147483647) ∧ (888623889 < 2147483647 ∧ 1163898945 < 2147483647); omega) canonical15 (by rfl)
#print axioms add15
theorem mul14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1599780737#u32 2105233088#u32 1384773872#u32 177371747#u32) (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32)=ok (q 756954712#u32 1152152674#u32 2085484832#u32 1236802420#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1599780737 < 2147483647 ∧ 2105233088 < 2147483647) ∧ (1384773872 < 2147483647 ∧ 177371747 < 2147483647); omega) (by change (528783666 < 2147483647 ∧ 1672539309 < 2147483647) ∧ (1274387717 < 2147483647 ∧ 552414171 < 2147483647); omega) (by rfl)
#print axioms mul14
theorem add14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 756954712#u32 1152152674#u32 2085484832#u32 1236802420#u32) c14=ok (q 1299681090#u32 731504958#u32 196634121#u32 1544879166#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (756954712 < 2147483647 ∧ 1152152674 < 2147483647) ∧ (2085484832 < 2147483647 ∧ 1236802420 < 2147483647); omega) canonical14 (by rfl)
#print axioms add14
def final : Q := (q 1299681090#u32 731504958#u32 196634121#u32 1544879166#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 1#usize 28#usize initial 14#usize final := by
  refine .step (by change 28>0; omega) (JFr_IndexArithmetic.sub 28#usize 27#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32) from rfl) mul27 (show Array.index_usize p 27#usize=ok c27 from rfl) add27 ?_
  refine .step (by change 27>0; omega) (JFr_IndexArithmetic.sub 27#usize 26#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32) from rfl) mul26 (show Array.index_usize p 26#usize=ok c26 from rfl) add26 ?_
  refine .step (by change 26>0; omega) (JFr_IndexArithmetic.sub 26#usize 25#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32) from rfl) mul25 (show Array.index_usize p 25#usize=ok c25 from rfl) add25 ?_
  refine .step (by change 25>0; omega) (JFr_IndexArithmetic.sub 25#usize 24#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32) from rfl) mul24 (show Array.index_usize p 24#usize=ok c24 from rfl) add24 ?_
  refine .step (by change 24>0; omega) (JFr_IndexArithmetic.sub 24#usize 23#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32) from rfl) mul23 (show Array.index_usize p 23#usize=ok c23 from rfl) add23 ?_
  refine .step (by change 23>0; omega) (JFr_IndexArithmetic.sub 23#usize 22#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32) from rfl) mul22 (show Array.index_usize p 22#usize=ok c22 from rfl) add22 ?_
  refine .step (by change 22>0; omega) (JFr_IndexArithmetic.sub 22#usize 21#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32) from rfl) mul21 (show Array.index_usize p 21#usize=ok c21 from rfl) add21 ?_
  refine .step (by change 21>0; omega) (JFr_IndexArithmetic.sub 21#usize 20#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32) from rfl) mul20 (show Array.index_usize p 20#usize=ok c20 from rfl) add20 ?_
  refine .step (by change 20>0; omega) (JFr_IndexArithmetic.sub 20#usize 19#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32) from rfl) mul19 (show Array.index_usize p 19#usize=ok c19 from rfl) add19 ?_
  refine .step (by change 19>0; omega) (JFr_IndexArithmetic.sub 19#usize 18#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32) from rfl) mul18 (show Array.index_usize p 18#usize=ok c18 from rfl) add18 ?_
  refine .step (by change 18>0; omega) (JFr_IndexArithmetic.sub 18#usize 17#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32) from rfl) mul17 (show Array.index_usize p 17#usize=ok c17 from rfl) add17 ?_
  refine .step (by change 17>0; omega) (JFr_IndexArithmetic.sub 17#usize 16#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32) from rfl) mul16 (show Array.index_usize p 16#usize=ok c16 from rfl) add16 ?_
  refine .step (by change 16>0; omega) (JFr_IndexArithmetic.sub 16#usize 15#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32) from rfl) mul15 (show Array.index_usize p 15#usize=ok c15 from rfl) add15 ?_
  refine .step (by change 15>0; omega) (JFr_IndexArithmetic.sub 15#usize 14#usize rfl) (show Array.index_usize alpha 1#usize=ok (q 528783666#u32 1672539309#u32 1274387717#u32 552414171#u32) from rfl) mul14 (show Array.index_usize p 14#usize=ok c14 from rfl) add14 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner01_0
