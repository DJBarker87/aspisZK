import NDO_JFr_Data09
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner09_0
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data09
def initial : Q := (q 0#u32 0#u32 0#u32 0#u32)
theorem mul27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 0#u32 0#u32 0#u32 0#u32) (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32)=ok (q 0#u32 0#u32 0#u32 0#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) (by change (1088201115 < 2147483647 ∧ 1292966428 < 2147483647) ∧ (495022806 < 2147483647 ∧ 1713251341 < 2147483647); omega) (by rfl)
#print axioms mul27
theorem add27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 0#u32 0#u32 0#u32 0#u32) c27=ok (q 1471006646#u32 1883759708#u32 1711760852#u32 1075465554#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) canonical27 (by rfl)
#print axioms add27
theorem mul26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1471006646#u32 1883759708#u32 1711760852#u32 1075465554#u32) (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32)=ok (q 776256933#u32 1410842478#u32 1889805777#u32 677468245#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1471006646 < 2147483647 ∧ 1883759708 < 2147483647) ∧ (1711760852 < 2147483647 ∧ 1075465554 < 2147483647); omega) (by change (1088201115 < 2147483647 ∧ 1292966428 < 2147483647) ∧ (495022806 < 2147483647 ∧ 1713251341 < 2147483647); omega) (by rfl)
#print axioms mul26
theorem add26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 776256933#u32 1410842478#u32 1889805777#u32 677468245#u32) c26=ok (q 940378994#u32 374833120#u32 1868902317#u32 2060694037#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (776256933 < 2147483647 ∧ 1410842478 < 2147483647) ∧ (1889805777 < 2147483647 ∧ 677468245 < 2147483647); omega) canonical26 (by rfl)
#print axioms add26
theorem mul25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 940378994#u32 374833120#u32 1868902317#u32 2060694037#u32) (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32)=ok (q 2001280334#u32 1071225461#u32 1336272074#u32 224618151#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (940378994 < 2147483647 ∧ 374833120 < 2147483647) ∧ (1868902317 < 2147483647 ∧ 2060694037 < 2147483647); omega) (by change (1088201115 < 2147483647 ∧ 1292966428 < 2147483647) ∧ (495022806 < 2147483647 ∧ 1713251341 < 2147483647); omega) (by rfl)
#print axioms mul25
theorem add25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2001280334#u32 1071225461#u32 1336272074#u32 224618151#u32) c25=ok (q 1753884759#u32 1817727741#u32 28718248#u32 150072238#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2001280334 < 2147483647 ∧ 1071225461 < 2147483647) ∧ (1336272074 < 2147483647 ∧ 224618151 < 2147483647); omega) canonical25 (by rfl)
#print axioms add25
theorem mul24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1753884759#u32 1817727741#u32 28718248#u32 150072238#u32) (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32)=ok (q 2092421334#u32 839622433#u32 964573006#u32 1170392777#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1753884759 < 2147483647 ∧ 1817727741 < 2147483647) ∧ (28718248 < 2147483647 ∧ 150072238 < 2147483647); omega) (by change (1088201115 < 2147483647 ∧ 1292966428 < 2147483647) ∧ (495022806 < 2147483647 ∧ 1713251341 < 2147483647); omega) (by rfl)
#print axioms mul24
theorem add24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2092421334#u32 839622433#u32 964573006#u32 1170392777#u32) c24=ok (q 1068900186#u32 1452915648#u32 1680169124#u32 1665849265#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2092421334 < 2147483647 ∧ 839622433 < 2147483647) ∧ (964573006 < 2147483647 ∧ 1170392777 < 2147483647); omega) canonical24 (by rfl)
#print axioms add24
theorem mul23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1068900186#u32 1452915648#u32 1680169124#u32 1665849265#u32) (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32)=ok (q 626260969#u32 2099643491#u32 1557908273#u32 243722883#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1068900186 < 2147483647 ∧ 1452915648 < 2147483647) ∧ (1680169124 < 2147483647 ∧ 1665849265 < 2147483647); omega) (by change (1088201115 < 2147483647 ∧ 1292966428 < 2147483647) ∧ (495022806 < 2147483647 ∧ 1713251341 < 2147483647); omega) (by rfl)
#print axioms mul23
theorem add23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 626260969#u32 2099643491#u32 1557908273#u32 243722883#u32) c23=ok (q 916230187#u32 1768713660#u32 1769078687#u32 171674407#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (626260969 < 2147483647 ∧ 2099643491 < 2147483647) ∧ (1557908273 < 2147483647 ∧ 243722883 < 2147483647); omega) canonical23 (by rfl)
#print axioms add23
theorem mul22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 916230187#u32 1768713660#u32 1769078687#u32 171674407#u32) (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32)=ok (q 559342438#u32 1608374567#u32 1085818743#u32 1042126152#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (916230187 < 2147483647 ∧ 1768713660 < 2147483647) ∧ (1769078687 < 2147483647 ∧ 171674407 < 2147483647); omega) (by change (1088201115 < 2147483647 ∧ 1292966428 < 2147483647) ∧ (495022806 < 2147483647 ∧ 1713251341 < 2147483647); omega) (by rfl)
#print axioms mul22
theorem add22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 559342438#u32 1608374567#u32 1085818743#u32 1042126152#u32) c22=ok (q 341144766#u32 156407654#u32 1625282898#u32 1847745220#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (559342438 < 2147483647 ∧ 1608374567 < 2147483647) ∧ (1085818743 < 2147483647 ∧ 1042126152 < 2147483647); omega) canonical22 (by rfl)
#print axioms add22
theorem mul21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 341144766#u32 156407654#u32 1625282898#u32 1847745220#u32) (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32)=ok (q 507563213#u32 437905789#u32 141618208#u32 364222194#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (341144766 < 2147483647 ∧ 156407654 < 2147483647) ∧ (1625282898 < 2147483647 ∧ 1847745220 < 2147483647); omega) (by change (1088201115 < 2147483647 ∧ 1292966428 < 2147483647) ∧ (495022806 < 2147483647 ∧ 1713251341 < 2147483647); omega) (by rfl)
#print axioms mul21
theorem add21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 507563213#u32 437905789#u32 141618208#u32 364222194#u32) c21=ok (q 1339380327#u32 923042300#u32 436428511#u32 2133586340#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (507563213 < 2147483647 ∧ 437905789 < 2147483647) ∧ (141618208 < 2147483647 ∧ 364222194 < 2147483647); omega) canonical21 (by rfl)
#print axioms add21
theorem mul20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1339380327#u32 923042300#u32 436428511#u32 2133586340#u32) (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32)=ok (q 1254834288#u32 2138393189#u32 1763503734#u32 1122903503#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1339380327 < 2147483647 ∧ 923042300 < 2147483647) ∧ (436428511 < 2147483647 ∧ 2133586340 < 2147483647); omega) (by change (1088201115 < 2147483647 ∧ 1292966428 < 2147483647) ∧ (495022806 < 2147483647 ∧ 1713251341 < 2147483647); omega) (by rfl)
#print axioms mul20
theorem add20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1254834288#u32 2138393189#u32 1763503734#u32 1122903503#u32) c20=ok (q 215653207#u32 84071536#u32 906544674#u32 1090683543#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1254834288 < 2147483647 ∧ 2138393189 < 2147483647) ∧ (1763503734 < 2147483647 ∧ 1122903503 < 2147483647); omega) canonical20 (by rfl)
#print axioms add20
theorem mul19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 215653207#u32 84071536#u32 906544674#u32 1090683543#u32) (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32)=ok (q 158886734#u32 803074804#u32 224670977#u32 1496284255#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (215653207 < 2147483647 ∧ 84071536 < 2147483647) ∧ (906544674 < 2147483647 ∧ 1090683543 < 2147483647); omega) (by change (1088201115 < 2147483647 ∧ 1292966428 < 2147483647) ∧ (495022806 < 2147483647 ∧ 1713251341 < 2147483647); omega) (by rfl)
#print axioms mul19
theorem add19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 158886734#u32 803074804#u32 224670977#u32 1496284255#u32) c19=ok (q 354750065#u32 1251108386#u32 1373958848#u32 517417367#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (158886734 < 2147483647 ∧ 803074804 < 2147483647) ∧ (224670977 < 2147483647 ∧ 1496284255 < 2147483647); omega) canonical19 (by rfl)
#print axioms add19
theorem mul18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 354750065#u32 1251108386#u32 1373958848#u32 517417367#u32) (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32)=ok (q 263404210#u32 1292381862#u32 90302398#u32 1271453441#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (354750065 < 2147483647 ∧ 1251108386 < 2147483647) ∧ (1373958848 < 2147483647 ∧ 517417367 < 2147483647); omega) (by change (1088201115 < 2147483647 ∧ 1292966428 < 2147483647) ∧ (495022806 < 2147483647 ∧ 1713251341 < 2147483647); omega) (by rfl)
#print axioms mul18
theorem add18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 263404210#u32 1292381862#u32 90302398#u32 1271453441#u32) c18=ok (q 326326064#u32 1540502491#u32 1539965216#u32 398185001#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (263404210 < 2147483647 ∧ 1292381862 < 2147483647) ∧ (90302398 < 2147483647 ∧ 1271453441 < 2147483647); omega) canonical18 (by rfl)
#print axioms add18
theorem mul17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 326326064#u32 1540502491#u32 1539965216#u32 398185001#u32) (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32)=ok (q 791942355#u32 1158300104#u32 1797797970#u32 1549207522#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (326326064 < 2147483647 ∧ 1540502491 < 2147483647) ∧ (1539965216 < 2147483647 ∧ 398185001 < 2147483647); omega) (by change (1088201115 < 2147483647 ∧ 1292966428 < 2147483647) ∧ (495022806 < 2147483647 ∧ 1713251341 < 2147483647); omega) (by rfl)
#print axioms mul17
theorem add17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 791942355#u32 1158300104#u32 1797797970#u32 1549207522#u32) c17=ok (q 447080969#u32 655766357#u32 629754159#u32 2067363600#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (791942355 < 2147483647 ∧ 1158300104 < 2147483647) ∧ (1797797970 < 2147483647 ∧ 1549207522 < 2147483647); omega) canonical17 (by rfl)
#print axioms add17
theorem mul16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 447080969#u32 655766357#u32 629754159#u32 2067363600#u32) (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32)=ok (q 243381243#u32 611756917#u32 2080850812#u32 1358012183#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (447080969 < 2147483647 ∧ 655766357 < 2147483647) ∧ (629754159 < 2147483647 ∧ 2067363600 < 2147483647); omega) (by change (1088201115 < 2147483647 ∧ 1292966428 < 2147483647) ∧ (495022806 < 2147483647 ∧ 1713251341 < 2147483647); omega) (by rfl)
#print axioms mul16
theorem add16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 243381243#u32 611756917#u32 2080850812#u32 1358012183#u32) c16=ok (q 42645054#u32 2096015959#u32 1021357993#u32 1085233475#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (243381243 < 2147483647 ∧ 611756917 < 2147483647) ∧ (2080850812 < 2147483647 ∧ 1358012183 < 2147483647); omega) canonical16 (by rfl)
#print axioms add16
theorem mul15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 42645054#u32 2096015959#u32 1021357993#u32 1085233475#u32) (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32)=ok (q 1525611345#u32 1180010015#u32 905228184#u32 1592504369#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (42645054 < 2147483647 ∧ 2096015959 < 2147483647) ∧ (1021357993 < 2147483647 ∧ 1085233475 < 2147483647); omega) (by change (1088201115 < 2147483647 ∧ 1292966428 < 2147483647) ∧ (495022806 < 2147483647 ∧ 1713251341 < 2147483647); omega) (by rfl)
#print axioms mul15
theorem add15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1525611345#u32 1180010015#u32 905228184#u32 1592504369#u32) c15=ok (q 30230597#u32 1369443751#u32 1373605717#u32 1870386528#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1525611345 < 2147483647 ∧ 1180010015 < 2147483647) ∧ (905228184 < 2147483647 ∧ 1592504369 < 2147483647); omega) canonical15 (by rfl)
#print axioms add15
theorem mul14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 30230597#u32 1369443751#u32 1373605717#u32 1870386528#u32) (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32)=ok (q 793338146#u32 1166912385#u32 1250832995#u32 907041347#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (30230597 < 2147483647 ∧ 1369443751 < 2147483647) ∧ (1373605717 < 2147483647 ∧ 1870386528 < 2147483647); omega) (by change (1088201115 < 2147483647 ∧ 1292966428 < 2147483647) ∧ (495022806 < 2147483647 ∧ 1713251341 < 2147483647); omega) (by rfl)
#print axioms mul14
theorem add14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 793338146#u32 1166912385#u32 1250832995#u32 907041347#u32) c14=ok (q 1913119858#u32 1966863962#u32 967324423#u32 1348006761#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (793338146 < 2147483647 ∧ 1166912385 < 2147483647) ∧ (1250832995 < 2147483647 ∧ 907041347 < 2147483647); omega) canonical14 (by rfl)
#print axioms add14
def final : Q := (q 1913119858#u32 1966863962#u32 967324423#u32 1348006761#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 9#usize 28#usize initial 14#usize final := by
  refine .step (by change 28>0; omega) (JFr_IndexArithmetic.sub 28#usize 27#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32) from rfl) mul27 (show Array.index_usize p 27#usize=ok c27 from rfl) add27 ?_
  refine .step (by change 27>0; omega) (JFr_IndexArithmetic.sub 27#usize 26#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32) from rfl) mul26 (show Array.index_usize p 26#usize=ok c26 from rfl) add26 ?_
  refine .step (by change 26>0; omega) (JFr_IndexArithmetic.sub 26#usize 25#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32) from rfl) mul25 (show Array.index_usize p 25#usize=ok c25 from rfl) add25 ?_
  refine .step (by change 25>0; omega) (JFr_IndexArithmetic.sub 25#usize 24#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32) from rfl) mul24 (show Array.index_usize p 24#usize=ok c24 from rfl) add24 ?_
  refine .step (by change 24>0; omega) (JFr_IndexArithmetic.sub 24#usize 23#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32) from rfl) mul23 (show Array.index_usize p 23#usize=ok c23 from rfl) add23 ?_
  refine .step (by change 23>0; omega) (JFr_IndexArithmetic.sub 23#usize 22#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32) from rfl) mul22 (show Array.index_usize p 22#usize=ok c22 from rfl) add22 ?_
  refine .step (by change 22>0; omega) (JFr_IndexArithmetic.sub 22#usize 21#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32) from rfl) mul21 (show Array.index_usize p 21#usize=ok c21 from rfl) add21 ?_
  refine .step (by change 21>0; omega) (JFr_IndexArithmetic.sub 21#usize 20#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32) from rfl) mul20 (show Array.index_usize p 20#usize=ok c20 from rfl) add20 ?_
  refine .step (by change 20>0; omega) (JFr_IndexArithmetic.sub 20#usize 19#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32) from rfl) mul19 (show Array.index_usize p 19#usize=ok c19 from rfl) add19 ?_
  refine .step (by change 19>0; omega) (JFr_IndexArithmetic.sub 19#usize 18#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32) from rfl) mul18 (show Array.index_usize p 18#usize=ok c18 from rfl) add18 ?_
  refine .step (by change 18>0; omega) (JFr_IndexArithmetic.sub 18#usize 17#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32) from rfl) mul17 (show Array.index_usize p 17#usize=ok c17 from rfl) add17 ?_
  refine .step (by change 17>0; omega) (JFr_IndexArithmetic.sub 17#usize 16#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32) from rfl) mul16 (show Array.index_usize p 16#usize=ok c16 from rfl) add16 ?_
  refine .step (by change 16>0; omega) (JFr_IndexArithmetic.sub 16#usize 15#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32) from rfl) mul15 (show Array.index_usize p 15#usize=ok c15 from rfl) add15 ?_
  refine .step (by change 15>0; omega) (JFr_IndexArithmetic.sub 15#usize 14#usize rfl) (show Array.index_usize alpha 9#usize=ok (q 1088201115#u32 1292966428#u32 495022806#u32 1713251341#u32) from rfl) mul14 (show Array.index_usize p 14#usize=ok c14 from rfl) add14 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner09_0
