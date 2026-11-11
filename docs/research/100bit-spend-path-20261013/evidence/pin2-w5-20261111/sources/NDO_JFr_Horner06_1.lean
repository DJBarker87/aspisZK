import NDO_JFr_Data06
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner06_1
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data06
def initial : Q := (q 909970829#u32 1021909394#u32 2140305673#u32 1110630357#u32)
theorem mul13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 909970829#u32 1021909394#u32 2140305673#u32 1110630357#u32) (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32)=ok (q 769512382#u32 651840118#u32 1440525508#u32 1727573880#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (909970829 < 2147483647 ∧ 1021909394 < 2147483647) ∧ (2140305673 < 2147483647 ∧ 1110630357 < 2147483647); omega) (by change (270702945 < 2147483647 ∧ 1582130923 < 2147483647) ∧ (1873897156 < 2147483647 ∧ 1411904894 < 2147483647); omega) (by rfl)
#print axioms mul13
theorem add13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 769512382#u32 651840118#u32 1440525508#u32 1727573880#u32) c13=ok (q 1435210507#u32 1152590154#u32 993477449#u32 1882515072#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (769512382 < 2147483647 ∧ 651840118 < 2147483647) ∧ (1440525508 < 2147483647 ∧ 1727573880 < 2147483647); omega) canonical13 (by rfl)
#print axioms add13
theorem mul12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1435210507#u32 1152590154#u32 993477449#u32 1882515072#u32) (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32)=ok (q 398585436#u32 209091786#u32 1375410663#u32 468631550#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1435210507 < 2147483647 ∧ 1152590154 < 2147483647) ∧ (993477449 < 2147483647 ∧ 1882515072 < 2147483647); omega) (by change (270702945 < 2147483647 ∧ 1582130923 < 2147483647) ∧ (1873897156 < 2147483647 ∧ 1411904894 < 2147483647); omega) (by rfl)
#print axioms mul12
theorem add12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 398585436#u32 209091786#u32 1375410663#u32 468631550#u32) c12=ok (q 873418439#u32 859258687#u32 209105847#u32 88870007#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (398585436 < 2147483647 ∧ 209091786 < 2147483647) ∧ (1375410663 < 2147483647 ∧ 468631550 < 2147483647); omega) canonical12 (by rfl)
#print axioms add12
theorem mul11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 873418439#u32 859258687#u32 209105847#u32 88870007#u32) (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32)=ok (q 1971893923#u32 1263080772#u32 954999023#u32 968904791#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (873418439 < 2147483647 ∧ 859258687 < 2147483647) ∧ (209105847 < 2147483647 ∧ 88870007 < 2147483647); omega) (by change (270702945 < 2147483647 ∧ 1582130923 < 2147483647) ∧ (1873897156 < 2147483647 ∧ 1411904894 < 2147483647); omega) (by rfl)
#print axioms mul11
theorem add11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1971893923#u32 1263080772#u32 954999023#u32 968904791#u32) c11=ok (q 640196894#u32 508309989#u32 1583095124#u32 2075030644#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1971893923 < 2147483647 ∧ 1263080772 < 2147483647) ∧ (954999023 < 2147483647 ∧ 968904791 < 2147483647); omega) canonical11 (by rfl)
#print axioms add11
theorem mul10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 640196894#u32 508309989#u32 1583095124#u32 2075030644#u32) (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32)=ok (q 1707444991#u32 1754007161#u32 1127583580#u32 1133503061#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (640196894 < 2147483647 ∧ 508309989 < 2147483647) ∧ (1583095124 < 2147483647 ∧ 2075030644 < 2147483647); omega) (by change (270702945 < 2147483647 ∧ 1582130923 < 2147483647) ∧ (1873897156 < 2147483647 ∧ 1411904894 < 2147483647); omega) (by rfl)
#print axioms mul10
theorem add10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1707444991#u32 1754007161#u32 1127583580#u32 1133503061#u32) c10=ok (q 291683183#u32 812991590#u32 1054696458#u32 253875432#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1707444991 < 2147483647 ∧ 1754007161 < 2147483647) ∧ (1127583580 < 2147483647 ∧ 1133503061 < 2147483647); omega) canonical10 (by rfl)
#print axioms add10
theorem mul09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 291683183#u32 812991590#u32 1054696458#u32 253875432#u32) (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32)=ok (q 1779037942#u32 1639372206#u32 1186578647#u32 744136844#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (291683183 < 2147483647 ∧ 812991590 < 2147483647) ∧ (1054696458 < 2147483647 ∧ 253875432 < 2147483647); omega) (by change (270702945 < 2147483647 ∧ 1582130923 < 2147483647) ∧ (1873897156 < 2147483647 ∧ 1411904894 < 2147483647); omega) (by rfl)
#print axioms mul09
theorem add09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1779037942#u32 1639372206#u32 1186578647#u32 744136844#u32) c09=ok (q 2021539727#u32 1459798416#u32 57086936#u32 302849338#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1779037942 < 2147483647 ∧ 1639372206 < 2147483647) ∧ (1186578647 < 2147483647 ∧ 744136844 < 2147483647); omega) canonical09 (by rfl)
#print axioms add09
theorem mul08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2021539727#u32 1459798416#u32 57086936#u32 302849338#u32) (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32)=ok (q 999003254#u32 1000638292#u32 366673657#u32 1864390#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2021539727 < 2147483647 ∧ 1459798416 < 2147483647) ∧ (57086936 < 2147483647 ∧ 302849338 < 2147483647); omega) (by change (270702945 < 2147483647 ∧ 1582130923 < 2147483647) ∧ (1873897156 < 2147483647 ∧ 1411904894 < 2147483647); omega) (by rfl)
#print axioms mul08
theorem add08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 999003254#u32 1000638292#u32 366673657#u32 1864390#u32) c08=ok (q 1297700908#u32 1974807838#u32 1698153916#u32 1839856055#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (999003254 < 2147483647 ∧ 1000638292 < 2147483647) ∧ (366673657 < 2147483647 ∧ 1864390 < 2147483647); omega) canonical08 (by rfl)
#print axioms add08
theorem mul07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1297700908#u32 1974807838#u32 1698153916#u32 1839856055#u32) (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32)=ok (q 1119321372#u32 1013863764#u32 47217848#u32 1223655183#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1297700908 < 2147483647 ∧ 1974807838 < 2147483647) ∧ (1698153916 < 2147483647 ∧ 1839856055 < 2147483647); omega) (by change (270702945 < 2147483647 ∧ 1582130923 < 2147483647) ∧ (1873897156 < 2147483647 ∧ 1411904894 < 2147483647); omega) (by rfl)
#print axioms mul07
theorem add07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1119321372#u32 1013863764#u32 47217848#u32 1223655183#u32) c07=ok (q 1440334371#u32 968398153#u32 1687330789#u32 1924460896#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1119321372 < 2147483647 ∧ 1013863764 < 2147483647) ∧ (47217848 < 2147483647 ∧ 1223655183 < 2147483647); omega) canonical07 (by rfl)
#print axioms add07
theorem mul06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1440334371#u32 968398153#u32 1687330789#u32 1924460896#u32) (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32)=ok (q 925095995#u32 1692248731#u32 200461851#u32 733162582#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1440334371 < 2147483647 ∧ 968398153 < 2147483647) ∧ (1687330789 < 2147483647 ∧ 1924460896 < 2147483647); omega) (by change (270702945 < 2147483647 ∧ 1582130923 < 2147483647) ∧ (1873897156 < 2147483647 ∧ 1411904894 < 2147483647); omega) (by rfl)
#print axioms mul06
theorem add06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 925095995#u32 1692248731#u32 200461851#u32 733162582#u32) c06=ok (q 1474308742#u32 2092470372#u32 1251612070#u32 1415100454#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (925095995 < 2147483647 ∧ 1692248731 < 2147483647) ∧ (200461851 < 2147483647 ∧ 733162582 < 2147483647); omega) canonical06 (by rfl)
#print axioms add06
theorem mul05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1474308742#u32 2092470372#u32 1251612070#u32 1415100454#u32) (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32)=ok (q 1055003551#u32 577988836#u32 134663733#u32 56077271#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1474308742 < 2147483647 ∧ 2092470372 < 2147483647) ∧ (1251612070 < 2147483647 ∧ 1415100454 < 2147483647); omega) (by change (270702945 < 2147483647 ∧ 1582130923 < 2147483647) ∧ (1873897156 < 2147483647 ∧ 1411904894 < 2147483647); omega) (by rfl)
#print axioms mul05
theorem add05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1055003551#u32 577988836#u32 134663733#u32 56077271#u32) c05=ok (q 306741094#u32 2013843461#u32 1555568814#u32 1718890467#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1055003551 < 2147483647 ∧ 577988836 < 2147483647) ∧ (134663733 < 2147483647 ∧ 56077271 < 2147483647); omega) canonical05 (by rfl)
#print axioms add05
theorem mul04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 306741094#u32 2013843461#u32 1555568814#u32 1718890467#u32) (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32)=ok (q 344627386#u32 1310663978#u32 292795091#u32 103621765#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (306741094 < 2147483647 ∧ 2013843461 < 2147483647) ∧ (1555568814 < 2147483647 ∧ 1718890467 < 2147483647); omega) (by change (270702945 < 2147483647 ∧ 1582130923 < 2147483647) ∧ (1873897156 < 2147483647 ∧ 1411904894 < 2147483647); omega) (by rfl)
#print axioms mul04
theorem add04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 344627386#u32 1310663978#u32 292795091#u32 103621765#u32) c04=ok (q 216536864#u32 357075139#u32 1682521675#u32 483573341#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (344627386 < 2147483647 ∧ 1310663978 < 2147483647) ∧ (292795091 < 2147483647 ∧ 103621765 < 2147483647); omega) canonical04 (by rfl)
#print axioms add04
theorem mul03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 216536864#u32 357075139#u32 1682521675#u32 483573341#u32) (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32)=ok (q 1778769599#u32 214572735#u32 1561665514#u32 826310021#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (216536864 < 2147483647 ∧ 357075139 < 2147483647) ∧ (1682521675 < 2147483647 ∧ 483573341 < 2147483647); omega) (by change (270702945 < 2147483647 ∧ 1582130923 < 2147483647) ∧ (1873897156 < 2147483647 ∧ 1411904894 < 2147483647); omega) (by rfl)
#print axioms mul03
theorem add03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1778769599#u32 214572735#u32 1561665514#u32 826310021#u32) c03=ok (q 851428234#u32 1818843075#u32 1690606641#u32 1327641839#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1778769599 < 2147483647 ∧ 214572735 < 2147483647) ∧ (1561665514 < 2147483647 ∧ 826310021 < 2147483647); omega) canonical03 (by rfl)
#print axioms add03
theorem mul02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 851428234#u32 1818843075#u32 1690606641#u32 1327641839#u32) (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32)=ok (q 1892312147#u32 1971276131#u32 100337188#u32 1341540143#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (851428234 < 2147483647 ∧ 1818843075 < 2147483647) ∧ (1690606641 < 2147483647 ∧ 1327641839 < 2147483647); omega) (by change (270702945 < 2147483647 ∧ 1582130923 < 2147483647) ∧ (1873897156 < 2147483647 ∧ 1411904894 < 2147483647); omega) (by rfl)
#print axioms mul02
theorem add02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1892312147#u32 1971276131#u32 100337188#u32 1341540143#u32) c02=ok (q 367123976#u32 150793082#u32 708163610#u32 1450820072#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1892312147 < 2147483647 ∧ 1971276131 < 2147483647) ∧ (100337188 < 2147483647 ∧ 1341540143 < 2147483647); omega) canonical02 (by rfl)
#print axioms add02
theorem mul01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 367123976#u32 150793082#u32 708163610#u32 1450820072#u32) (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32)=ok (q 1984424415#u32 1647564503#u32 1901213249#u32 1530837869#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (367123976 < 2147483647 ∧ 150793082 < 2147483647) ∧ (708163610 < 2147483647 ∧ 1450820072 < 2147483647); omega) (by change (270702945 < 2147483647 ∧ 1582130923 < 2147483647) ∧ (1873897156 < 2147483647 ∧ 1411904894 < 2147483647); omega) (by rfl)
#print axioms mul01
theorem add01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1984424415#u32 1647564503#u32 1901213249#u32 1530837869#u32) c01=ok (q 499680451#u32 1127900549#u32 241647947#u32 906154196#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1984424415 < 2147483647 ∧ 1647564503 < 2147483647) ∧ (1901213249 < 2147483647 ∧ 1530837869 < 2147483647); omega) canonical01 (by rfl)
#print axioms add01
theorem mul00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 499680451#u32 1127900549#u32 241647947#u32 906154196#u32) (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32)=ok (q 536963124#u32 327017934#u32 1752328698#u32 1788905037#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (499680451 < 2147483647 ∧ 1127900549 < 2147483647) ∧ (241647947 < 2147483647 ∧ 906154196 < 2147483647); omega) (by change (270702945 < 2147483647 ∧ 1582130923 < 2147483647) ∧ (1873897156 < 2147483647 ∧ 1411904894 < 2147483647); omega) (by rfl)
#print axioms mul00
theorem add00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 536963124#u32 327017934#u32 1752328698#u32 1788905037#u32) c00=ok (q 1422645336#u32 1223911572#u32 1186256290#u32 1882658550#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (536963124 < 2147483647 ∧ 327017934 < 2147483647) ∧ (1752328698 < 2147483647 ∧ 1788905037 < 2147483647); omega) canonical00 (by rfl)
#print axioms add00
def final : Q := (q 1422645336#u32 1223911572#u32 1186256290#u32 1882658550#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 6#usize 14#usize initial 0#usize final := by
  refine .step (by change 14>0; omega) (JFr_IndexArithmetic.sub 14#usize 13#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32) from rfl) mul13 (show Array.index_usize p 13#usize=ok c13 from rfl) add13 ?_
  refine .step (by change 13>0; omega) (JFr_IndexArithmetic.sub 13#usize 12#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32) from rfl) mul12 (show Array.index_usize p 12#usize=ok c12 from rfl) add12 ?_
  refine .step (by change 12>0; omega) (JFr_IndexArithmetic.sub 12#usize 11#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32) from rfl) mul11 (show Array.index_usize p 11#usize=ok c11 from rfl) add11 ?_
  refine .step (by change 11>0; omega) (JFr_IndexArithmetic.sub 11#usize 10#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32) from rfl) mul10 (show Array.index_usize p 10#usize=ok c10 from rfl) add10 ?_
  refine .step (by change 10>0; omega) (JFr_IndexArithmetic.sub 10#usize 9#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32) from rfl) mul09 (show Array.index_usize p 9#usize=ok c09 from rfl) add09 ?_
  refine .step (by change 9>0; omega) (JFr_IndexArithmetic.sub 9#usize 8#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32) from rfl) mul08 (show Array.index_usize p 8#usize=ok c08 from rfl) add08 ?_
  refine .step (by change 8>0; omega) (JFr_IndexArithmetic.sub 8#usize 7#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32) from rfl) mul07 (show Array.index_usize p 7#usize=ok c07 from rfl) add07 ?_
  refine .step (by change 7>0; omega) (JFr_IndexArithmetic.sub 7#usize 6#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32) from rfl) mul06 (show Array.index_usize p 6#usize=ok c06 from rfl) add06 ?_
  refine .step (by change 6>0; omega) (JFr_IndexArithmetic.sub 6#usize 5#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32) from rfl) mul05 (show Array.index_usize p 5#usize=ok c05 from rfl) add05 ?_
  refine .step (by change 5>0; omega) (JFr_IndexArithmetic.sub 5#usize 4#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32) from rfl) mul04 (show Array.index_usize p 4#usize=ok c04 from rfl) add04 ?_
  refine .step (by change 4>0; omega) (JFr_IndexArithmetic.sub 4#usize 3#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32) from rfl) mul03 (show Array.index_usize p 3#usize=ok c03 from rfl) add03 ?_
  refine .step (by change 3>0; omega) (JFr_IndexArithmetic.sub 3#usize 2#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32) from rfl) mul02 (show Array.index_usize p 2#usize=ok c02 from rfl) add02 ?_
  refine .step (by change 2>0; omega) (JFr_IndexArithmetic.sub 2#usize 1#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32) from rfl) mul01 (show Array.index_usize p 1#usize=ok c01 from rfl) add01 ?_
  refine .step (by change 1>0; omega) (JFr_IndexArithmetic.sub 1#usize 0#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 270702945#u32 1582130923#u32 1873897156#u32 1411904894#u32) from rfl) mul00 (show Array.index_usize p 0#usize=ok c00 from rfl) add00 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner06_1
