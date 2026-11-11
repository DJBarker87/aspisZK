import NDO_JFr_Data06
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner06_0
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data06
def initial : Q := (q 0#u32 0#u32 0#u32 0#u32)
theorem mul27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 0#u32 0#u32 0#u32 0#u32) (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32)=ok (q 0#u32 0#u32 0#u32 0#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) (by change (270702945 < 2147483647 ∧ 1582130923 < 2147483647) ∧ (1873897156 < 2147483647 ∧ 1411904894 < 2147483647); omega) (by rfl)
#print axioms mul27
theorem add27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 0#u32 0#u32 0#u32 0#u32) c27=ok (q 195901929#u32 1992274623#u32 380316084#u32 247044039#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) canonical27 (by rfl)
#print axioms add27
theorem mul26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 195901929#u32 1992274623#u32 380316084#u32 247044039#u32) (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32)=ok (q 128194854#u32 450444678#u32 1751451001#u32 1080794596#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (195901929 < 2147483647 ∧ 1992274623 < 2147483647) ∧ (380316084 < 2147483647 ∧ 247044039 < 2147483647); omega) (by change (270702945 < 2147483647 ∧ 1582130923 < 2147483647) ∧ (1873897156 < 2147483647 ∧ 1411904894 < 2147483647); omega) (by rfl)
#print axioms mul26
theorem add26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 128194854#u32 450444678#u32 1751451001#u32 1080794596#u32) c26=ok (q 1333726931#u32 2096195082#u32 1344974203#u32 1983413412#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (128194854 < 2147483647 ∧ 450444678 < 2147483647) ∧ (1751451001 < 2147483647 ∧ 1080794596 < 2147483647); omega) canonical26 (by rfl)
#print axioms add26
theorem mul25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1333726931#u32 2096195082#u32 1344974203#u32 1983413412#u32) (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32)=ok (q 1355429440#u32 888719995#u32 1722291565#u32 696016859#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1333726931 < 2147483647 ∧ 2096195082 < 2147483647) ∧ (1344974203 < 2147483647 ∧ 1983413412 < 2147483647); omega) (by change (270702945 < 2147483647 ∧ 1582130923 < 2147483647) ∧ (1873897156 < 2147483647 ∧ 1411904894 < 2147483647); omega) (by rfl)
#print axioms mul25
theorem add25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1355429440#u32 888719995#u32 1722291565#u32 696016859#u32) c25=ok (q 1631565659#u32 1692514705#u32 10472724#u32 345849722#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1355429440 < 2147483647 ∧ 888719995 < 2147483647) ∧ (1722291565 < 2147483647 ∧ 696016859 < 2147483647); omega) canonical25 (by rfl)
#print axioms add25
theorem mul24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1631565659#u32 1692514705#u32 10472724#u32 345849722#u32) (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32)=ok (q 987924420#u32 1273691568#u32 1389751574#u32 887165271#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1631565659 < 2147483647 ∧ 1692514705 < 2147483647) ∧ (10472724 < 2147483647 ∧ 345849722 < 2147483647); omega) (by change (270702945 < 2147483647 ∧ 1582130923 < 2147483647) ∧ (1873897156 < 2147483647 ∧ 1411904894 < 2147483647); omega) (by rfl)
#print axioms mul24
theorem add24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 987924420#u32 1273691568#u32 1389751574#u32 887165271#u32) c24=ok (q 1503615348#u32 1737284214#u32 1114732905#u32 519463160#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (987924420 < 2147483647 ∧ 1273691568 < 2147483647) ∧ (1389751574 < 2147483647 ∧ 887165271 < 2147483647); omega) canonical24 (by rfl)
#print axioms add24
theorem mul23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1503615348#u32 1737284214#u32 1114732905#u32 519463160#u32) (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32)=ok (q 1831888075#u32 1494578729#u32 1430474361#u32 1471116495#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1503615348 < 2147483647 ∧ 1737284214 < 2147483647) ∧ (1114732905 < 2147483647 ∧ 519463160 < 2147483647); omega) (by change (270702945 < 2147483647 ∧ 1582130923 < 2147483647) ∧ (1873897156 < 2147483647 ∧ 1411904894 < 2147483647); omega) (by rfl)
#print axioms mul23
theorem add23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1831888075#u32 1494578729#u32 1430474361#u32 1471116495#u32) c23=ok (q 1269517466#u32 120003059#u32 1597420496#u32 1781820418#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1831888075 < 2147483647 ∧ 1494578729 < 2147483647) ∧ (1430474361 < 2147483647 ∧ 1471116495 < 2147483647); omega) canonical23 (by rfl)
#print axioms add23
theorem mul22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1269517466#u32 120003059#u32 1597420496#u32 1781820418#u32) (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32)=ok (q 1657703058#u32 1535252159#u32 1395756934#u32 2097132197#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1269517466 < 2147483647 ∧ 120003059 < 2147483647) ∧ (1597420496 < 2147483647 ∧ 1781820418 < 2147483647); omega) (by change (270702945 < 2147483647 ∧ 1582130923 < 2147483647) ∧ (1873897156 < 2147483647 ∧ 1411904894 < 2147483647); omega) (by rfl)
#print axioms mul22
theorem add22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1657703058#u32 1535252159#u32 1395756934#u32 2097132197#u32) c22=ok (q 1430415389#u32 1481441104#u32 259120100#u32 1977154241#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1657703058 < 2147483647 ∧ 1535252159 < 2147483647) ∧ (1395756934 < 2147483647 ∧ 2097132197 < 2147483647); omega) canonical22 (by rfl)
#print axioms add22
theorem mul21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1430415389#u32 1481441104#u32 259120100#u32 1977154241#u32) (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32)=ok (q 1078307242#u32 521877735#u32 706609167#u32 478064227#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1430415389 < 2147483647 ∧ 1481441104 < 2147483647) ∧ (259120100 < 2147483647 ∧ 1977154241 < 2147483647); omega) (by change (270702945 < 2147483647 ∧ 1582130923 < 2147483647) ∧ (1873897156 < 2147483647 ∧ 1411904894 < 2147483647); omega) (by rfl)
#print axioms mul21
theorem add21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1078307242#u32 521877735#u32 706609167#u32 478064227#u32) c21=ok (q 823204512#u32 1737083321#u32 2147434720#u32 1201294833#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1078307242 < 2147483647 ∧ 521877735 < 2147483647) ∧ (706609167 < 2147483647 ∧ 478064227 < 2147483647); omega) canonical21 (by rfl)
#print axioms add21
theorem mul20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 823204512#u32 1737083321#u32 2147434720#u32 1201294833#u32) (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32)=ok (q 985924070#u32 689420452#u32 796043759#u32 194299740#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (823204512 < 2147483647 ∧ 1737083321 < 2147483647) ∧ (2147434720 < 2147483647 ∧ 1201294833 < 2147483647); omega) (by change (270702945 < 2147483647 ∧ 1582130923 < 2147483647) ∧ (1873897156 < 2147483647 ∧ 1411904894 < 2147483647); omega) (by rfl)
#print axioms mul20
theorem add20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 985924070#u32 689420452#u32 796043759#u32 194299740#u32) c20=ok (q 2039873572#u32 1265494678#u32 2121424091#u32 613760758#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (985924070 < 2147483647 ∧ 689420452 < 2147483647) ∧ (796043759 < 2147483647 ∧ 194299740 < 2147483647); omega) canonical20 (by rfl)
#print axioms add20
theorem mul19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2039873572#u32 1265494678#u32 2121424091#u32 613760758#u32) (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32)=ok (q 1259966547#u32 730341958#u32 1856527109#u32 1040352202#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2039873572 < 2147483647 ∧ 1265494678 < 2147483647) ∧ (2121424091 < 2147483647 ∧ 613760758 < 2147483647); omega) (by change (270702945 < 2147483647 ∧ 1582130923 < 2147483647) ∧ (1873897156 < 2147483647 ∧ 1411904894 < 2147483647); omega) (by rfl)
#print axioms mul19
theorem add19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1259966547#u32 730341958#u32 1856527109#u32 1040352202#u32) c19=ok (q 1581095363#u32 1590983063#u32 2071157079#u32 121804827#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1259966547 < 2147483647 ∧ 730341958 < 2147483647) ∧ (1856527109 < 2147483647 ∧ 1040352202 < 2147483647); omega) canonical19 (by rfl)
#print axioms add19
theorem mul18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1581095363#u32 1590983063#u32 2071157079#u32 121804827#u32) (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32)=ok (q 554654549#u32 2134185557#u32 1043595793#u32 61353512#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1581095363 < 2147483647 ∧ 1590983063 < 2147483647) ∧ (2071157079 < 2147483647 ∧ 121804827 < 2147483647); omega) (by change (270702945 < 2147483647 ∧ 1582130923 < 2147483647) ∧ (1873897156 < 2147483647 ∧ 1411904894 < 2147483647); omega) (by rfl)
#print axioms mul18
theorem add18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 554654549#u32 2134185557#u32 1043595793#u32 61353512#u32) c18=ok (q 141329468#u32 1534517311#u32 1308657535#u32 1585097023#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (554654549 < 2147483647 ∧ 2134185557 < 2147483647) ∧ (1043595793 < 2147483647 ∧ 61353512 < 2147483647); omega) canonical18 (by rfl)
#print axioms add18
theorem mul17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 141329468#u32 1534517311#u32 1308657535#u32 1585097023#u32) (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32)=ok (q 551417556#u32 764179479#u32 1007381096#u32 1785409277#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (141329468 < 2147483647 ∧ 1534517311 < 2147483647) ∧ (1308657535 < 2147483647 ∧ 1585097023 < 2147483647); omega) (by change (270702945 < 2147483647 ∧ 1582130923 < 2147483647) ∧ (1873897156 < 2147483647 ∧ 1411904894 < 2147483647); omega) (by rfl)
#print axioms mul17
theorem add17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 551417556#u32 764179479#u32 1007381096#u32 1785409277#u32) c17=ok (q 1840158615#u32 415142761#u32 867437580#u32 1013811223#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (551417556 < 2147483647 ∧ 764179479 < 2147483647) ∧ (1007381096 < 2147483647 ∧ 1785409277 < 2147483647); omega) canonical17 (by rfl)
#print axioms add17
theorem mul16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1840158615#u32 415142761#u32 867437580#u32 1013811223#u32) (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32)=ok (q 584083146#u32 1062184123#u32 274593258#u32 792648692#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1840158615 < 2147483647 ∧ 415142761 < 2147483647) ∧ (867437580 < 2147483647 ∧ 1013811223 < 2147483647); omega) (by change (270702945 < 2147483647 ∧ 1582130923 < 2147483647) ∧ (1873897156 < 2147483647 ∧ 1411904894 < 2147483647); omega) (by rfl)
#print axioms mul16
theorem add16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 584083146#u32 1062184123#u32 274593258#u32 792648692#u32) c16=ok (q 1563611082#u32 499589151#u32 2116177309#u32 2055570994#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (584083146 < 2147483647 ∧ 1062184123 < 2147483647) ∧ (274593258 < 2147483647 ∧ 792648692 < 2147483647); omega) canonical16 (by rfl)
#print axioms add16
theorem mul15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1563611082#u32 499589151#u32 2116177309#u32 2055570994#u32) (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32)=ok (q 2079381864#u32 1379697717#u32 141342970#u32 470334218#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1563611082 < 2147483647 ∧ 499589151 < 2147483647) ∧ (2116177309 < 2147483647 ∧ 2055570994 < 2147483647); omega) (by change (270702945 < 2147483647 ∧ 1582130923 < 2147483647) ∧ (1873897156 < 2147483647 ∧ 1411904894 < 2147483647); omega) (by rfl)
#print axioms mul15
theorem add15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2079381864#u32 1379697717#u32 141342970#u32 470334218#u32) c15=ok (q 458726245#u32 1397787340#u32 563377112#u32 2104636171#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2079381864 < 2147483647 ∧ 1379697717 < 2147483647) ∧ (141342970 < 2147483647 ∧ 470334218 < 2147483647); omega) canonical15 (by rfl)
#print axioms add15
theorem mul14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 458726245#u32 1397787340#u32 563377112#u32 2104636171#u32) (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32)=ok (q 1873931096#u32 1337008575#u32 953898036#u32 1310383231#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (458726245 < 2147483647 ∧ 1397787340 < 2147483647) ∧ (563377112 < 2147483647 ∧ 2104636171 < 2147483647); omega) (by change (270702945 < 2147483647 ∧ 1582130923 < 2147483647) ∧ (1873897156 < 2147483647 ∧ 1411904894 < 2147483647); omega) (by rfl)
#print axioms mul14
theorem add14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1873931096#u32 1337008575#u32 953898036#u32 1310383231#u32) c14=ok (q 909970829#u32 1021909394#u32 2140305673#u32 1110630357#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1873931096 < 2147483647 ∧ 1337008575 < 2147483647) ∧ (953898036 < 2147483647 ∧ 1310383231 < 2147483647); omega) canonical14 (by rfl)
#print axioms add14
def final : Q := (q 909970829#u32 1021909394#u32 2140305673#u32 1110630357#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 6#usize 28#usize initial 14#usize final := by
  refine .step (by change 28>0; omega) (JFr_IndexArithmetic.sub 28#usize 27#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32) from rfl) mul27 (show Array.index_usize p 27#usize=ok c27 from rfl) add27 ?_
  refine .step (by change 27>0; omega) (JFr_IndexArithmetic.sub 27#usize 26#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32) from rfl) mul26 (show Array.index_usize p 26#usize=ok c26 from rfl) add26 ?_
  refine .step (by change 26>0; omega) (JFr_IndexArithmetic.sub 26#usize 25#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32) from rfl) mul25 (show Array.index_usize p 25#usize=ok c25 from rfl) add25 ?_
  refine .step (by change 25>0; omega) (JFr_IndexArithmetic.sub 25#usize 24#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32) from rfl) mul24 (show Array.index_usize p 24#usize=ok c24 from rfl) add24 ?_
  refine .step (by change 24>0; omega) (JFr_IndexArithmetic.sub 24#usize 23#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32) from rfl) mul23 (show Array.index_usize p 23#usize=ok c23 from rfl) add23 ?_
  refine .step (by change 23>0; omega) (JFr_IndexArithmetic.sub 23#usize 22#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32) from rfl) mul22 (show Array.index_usize p 22#usize=ok c22 from rfl) add22 ?_
  refine .step (by change 22>0; omega) (JFr_IndexArithmetic.sub 22#usize 21#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32) from rfl) mul21 (show Array.index_usize p 21#usize=ok c21 from rfl) add21 ?_
  refine .step (by change 21>0; omega) (JFr_IndexArithmetic.sub 21#usize 20#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32) from rfl) mul20 (show Array.index_usize p 20#usize=ok c20 from rfl) add20 ?_
  refine .step (by change 20>0; omega) (JFr_IndexArithmetic.sub 20#usize 19#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32) from rfl) mul19 (show Array.index_usize p 19#usize=ok c19 from rfl) add19 ?_
  refine .step (by change 19>0; omega) (JFr_IndexArithmetic.sub 19#usize 18#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32) from rfl) mul18 (show Array.index_usize p 18#usize=ok c18 from rfl) add18 ?_
  refine .step (by change 18>0; omega) (JFr_IndexArithmetic.sub 18#usize 17#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32) from rfl) mul17 (show Array.index_usize p 17#usize=ok c17 from rfl) add17 ?_
  refine .step (by change 17>0; omega) (JFr_IndexArithmetic.sub 17#usize 16#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32) from rfl) mul16 (show Array.index_usize p 16#usize=ok c16 from rfl) add16 ?_
  refine .step (by change 16>0; omega) (JFr_IndexArithmetic.sub 16#usize 15#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32) from rfl) mul15 (show Array.index_usize p 15#usize=ok c15 from rfl) add15 ?_
  refine .step (by change 15>0; omega) (JFr_IndexArithmetic.sub 15#usize 14#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32) from rfl) mul14 (show Array.index_usize p 14#usize=ok c14 from rfl) add14 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner06_0
