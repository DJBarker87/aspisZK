import NDO_JFr_Data06
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner06_1
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data06
def initial : Q := (q 1321604998#u32 468043454#u32 1940954367#u32 1303357150#u32)
theorem mul13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1321604998#u32 468043454#u32 1940954367#u32 1303357150#u32) (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32)=ok (q 1329412675#u32 127031265#u32 473301135#u32 494206327#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1321604998 < 2147483647 ∧ 468043454 < 2147483647) ∧ (1940954367 < 2147483647 ∧ 1303357150 < 2147483647); omega) (by change (1410683225 < 2147483647 ∧ 375596669 < 2147483647) ∧ (973261870 < 2147483647 ∧ 122086709 < 2147483647); omega) (by rfl)
#print axioms mul13
theorem add13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1329412675#u32 127031265#u32 473301135#u32 494206327#u32) c13=ok (q 1416599466#u32 1148605661#u32 428034976#u32 1664715288#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1329412675 < 2147483647 ∧ 127031265 < 2147483647) ∧ (473301135 < 2147483647 ∧ 494206327 < 2147483647); omega) canonical13 (by rfl)
#print axioms add13
theorem mul12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1416599466#u32 1148605661#u32 428034976#u32 1664715288#u32) (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32)=ok (q 1624957281#u32 2042946034#u32 1358958903#u32 53982400#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1416599466 < 2147483647 ∧ 1148605661 < 2147483647) ∧ (428034976 < 2147483647 ∧ 1664715288 < 2147483647); omega) (by change (1410683225 < 2147483647 ∧ 375596669 < 2147483647) ∧ (973261870 < 2147483647 ∧ 122086709 < 2147483647); omega) (by rfl)
#print axioms mul12
theorem add12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1624957281#u32 2042946034#u32 1358958903#u32 53982400#u32) c12=ok (q 1127864627#u32 1574856263#u32 673293350#u32 635272062#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1624957281 < 2147483647 ∧ 2042946034 < 2147483647) ∧ (1358958903 < 2147483647 ∧ 53982400 < 2147483647); omega) canonical12 (by rfl)
#print axioms add12
theorem mul11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1127864627#u32 1574856263#u32 673293350#u32 635272062#u32) (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32)=ok (q 948281958#u32 2083548991#u32 1717040700#u32 1214439902#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1127864627 < 2147483647 ∧ 1574856263 < 2147483647) ∧ (673293350 < 2147483647 ∧ 635272062 < 2147483647); omega) (by change (1410683225 < 2147483647 ∧ 375596669 < 2147483647) ∧ (973261870 < 2147483647 ∧ 122086709 < 2147483647); omega) (by rfl)
#print axioms mul11
theorem add11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 948281958#u32 2083548991#u32 1717040700#u32 1214439902#u32) c11=ok (q 1727586183#u32 1955408561#u32 1118327560#u32 332816991#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (948281958 < 2147483647 ∧ 2083548991 < 2147483647) ∧ (1717040700 < 2147483647 ∧ 1214439902 < 2147483647); omega) canonical11 (by rfl)
#print axioms add11
theorem mul10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1727586183#u32 1955408561#u32 1118327560#u32 332816991#u32) (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32)=ok (q 1535425810#u32 1229287496#u32 870248187#u32 1083536822#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1727586183 < 2147483647 ∧ 1955408561 < 2147483647) ∧ (1118327560 < 2147483647 ∧ 332816991 < 2147483647); omega) (by change (1410683225 < 2147483647 ∧ 375596669 < 2147483647) ∧ (973261870 < 2147483647 ∧ 122086709 < 2147483647); omega) (by rfl)
#print axioms mul10
theorem add10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1535425810#u32 1229287496#u32 870248187#u32 1083536822#u32) c10=ok (q 1759445832#u32 1670380027#u32 989237055#u32 267192729#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1535425810 < 2147483647 ∧ 1229287496 < 2147483647) ∧ (870248187 < 2147483647 ∧ 1083536822 < 2147483647); omega) canonical10 (by rfl)
#print axioms add10
theorem mul09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1759445832#u32 1670380027#u32 989237055#u32 267192729#u32) (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32)=ok (q 211329775#u32 1808706875#u32 820176100#u32 78840983#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1759445832 < 2147483647 ∧ 1670380027 < 2147483647) ∧ (989237055 < 2147483647 ∧ 267192729 < 2147483647); omega) (by change (1410683225 < 2147483647 ∧ 375596669 < 2147483647) ∧ (973261870 < 2147483647 ∧ 122086709 < 2147483647); omega) (by rfl)
#print axioms mul09
theorem add09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 211329775#u32 1808706875#u32 820176100#u32 78840983#u32) c09=ok (q 1743449493#u32 1982101804#u32 1821033222#u32 981445783#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (211329775 < 2147483647 ∧ 1808706875 < 2147483647) ∧ (820176100 < 2147483647 ∧ 78840983 < 2147483647); omega) canonical09 (by rfl)
#print axioms add09
theorem mul08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1743449493#u32 1982101804#u32 1821033222#u32 981445783#u32) (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32)=ok (q 1107203691#u32 930767492#u32 1464019638#u32 1453403272#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1743449493 < 2147483647 ∧ 1982101804 < 2147483647) ∧ (1821033222 < 2147483647 ∧ 981445783 < 2147483647); omega) (by change (1410683225 < 2147483647 ∧ 375596669 < 2147483647) ∧ (973261870 < 2147483647 ∧ 122086709 < 2147483647); omega) (by rfl)
#print axioms mul08
theorem add08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1107203691#u32 930767492#u32 1464019638#u32 1453403272#u32) c08=ok (q 21451375#u32 1840724799#u32 798133424#u32 195060107#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1107203691 < 2147483647 ∧ 930767492 < 2147483647) ∧ (1464019638 < 2147483647 ∧ 1453403272 < 2147483647); omega) canonical08 (by rfl)
#print axioms add08
theorem mul07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 21451375#u32 1840724799#u32 798133424#u32 195060107#u32) (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32)=ok (q 882268589#u32 1744735431#u32 1948323868#u32 1170484642#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (21451375 < 2147483647 ∧ 1840724799 < 2147483647) ∧ (798133424 < 2147483647 ∧ 195060107 < 2147483647); omega) (by change (1410683225 < 2147483647 ∧ 375596669 < 2147483647) ∧ (973261870 < 2147483647 ∧ 122086709 < 2147483647); omega) (by rfl)
#print axioms mul07
theorem add07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 882268589#u32 1744735431#u32 1948323868#u32 1170484642#u32) c07=ok (q 1656587434#u32 799349214#u32 1326910441#u32 637421507#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (882268589 < 2147483647 ∧ 1744735431 < 2147483647) ∧ (1948323868 < 2147483647 ∧ 1170484642 < 2147483647); omega) canonical07 (by rfl)
#print axioms add07
theorem mul06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1656587434#u32 799349214#u32 1326910441#u32 637421507#u32) (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32)=ok (q 180161967#u32 1389423489#u32 1612252510#u32 2074245189#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1656587434 < 2147483647 ∧ 799349214 < 2147483647) ∧ (1326910441 < 2147483647 ∧ 637421507 < 2147483647); omega) (by change (1410683225 < 2147483647 ∧ 375596669 < 2147483647) ∧ (973261870 < 2147483647 ∧ 122086709 < 2147483647); omega) (by rfl)
#print axioms mul06
theorem add06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 180161967#u32 1389423489#u32 1612252510#u32 2074245189#u32) c06=ok (q 1355771325#u32 1232859712#u32 789840558#u32 84411177#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (180161967 < 2147483647 ∧ 1389423489 < 2147483647) ∧ (1612252510 < 2147483647 ∧ 2074245189 < 2147483647); omega) canonical06 (by rfl)
#print axioms add06
theorem mul05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1355771325#u32 1232859712#u32 789840558#u32 84411177#u32) (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32)=ok (q 652248979#u32 271929782#u32 1202405925#u32 1973773719#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1355771325 < 2147483647 ∧ 1232859712 < 2147483647) ∧ (789840558 < 2147483647 ∧ 84411177 < 2147483647); omega) (by change (1410683225 < 2147483647 ∧ 375596669 < 2147483647) ∧ (973261870 < 2147483647 ∧ 122086709 < 2147483647); omega) (by rfl)
#print axioms mul05
theorem add05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 652248979#u32 271929782#u32 1202405925#u32 1973773719#u32) c05=ok (q 979615313#u32 1284247650#u32 718309500#u32 481813030#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (652248979 < 2147483647 ∧ 271929782 < 2147483647) ∧ (1202405925 < 2147483647 ∧ 1973773719 < 2147483647); omega) canonical05 (by rfl)
#print axioms add05
theorem mul04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 979615313#u32 1284247650#u32 718309500#u32 481813030#u32) (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32)=ok (q 218882202#u32 1346241160#u32 1724373620#u32 523473#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (979615313 < 2147483647 ∧ 1284247650 < 2147483647) ∧ (718309500 < 2147483647 ∧ 481813030 < 2147483647); omega) (by change (1410683225 < 2147483647 ∧ 375596669 < 2147483647) ∧ (973261870 < 2147483647 ∧ 122086709 < 2147483647); omega) (by rfl)
#print axioms mul04
theorem add04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 218882202#u32 1346241160#u32 1724373620#u32 523473#u32) c04=ok (q 1917118741#u32 166059679#u32 1152926110#u32 1942025419#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (218882202 < 2147483647 ∧ 1346241160 < 2147483647) ∧ (1724373620 < 2147483647 ∧ 523473 < 2147483647); omega) canonical04 (by rfl)
#print axioms add04
theorem mul03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1917118741#u32 166059679#u32 1152926110#u32 1942025419#u32) (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32)=ok (q 734408744#u32 864013085#u32 300655839#u32 243191877#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1917118741 < 2147483647 ∧ 166059679 < 2147483647) ∧ (1152926110 < 2147483647 ∧ 1942025419 < 2147483647); omega) (by change (1410683225 < 2147483647 ∧ 375596669 < 2147483647) ∧ (973261870 < 2147483647 ∧ 122086709 < 2147483647); omega) (by rfl)
#print axioms mul03
theorem add03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 734408744#u32 864013085#u32 300655839#u32 243191877#u32) c03=ok (q 843531402#u32 324189468#u32 1690727363#u32 1076035134#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (734408744 < 2147483647 ∧ 864013085 < 2147483647) ∧ (300655839 < 2147483647 ∧ 243191877 < 2147483647); omega) canonical03 (by rfl)
#print axioms add03
theorem mul02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 843531402#u32 324189468#u32 1690727363#u32 1076035134#u32) (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32)=ok (q 1068177915#u32 1187963517#u32 369699898#u32 1881465080#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (843531402 < 2147483647 ∧ 324189468 < 2147483647) ∧ (1690727363 < 2147483647 ∧ 1076035134 < 2147483647); omega) (by change (1410683225 < 2147483647 ∧ 375596669 < 2147483647) ∧ (973261870 < 2147483647 ∧ 122086709 < 2147483647); omega) (by rfl)
#print axioms mul02
theorem add02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1068177915#u32 1187963517#u32 369699898#u32 1881465080#u32) c02=ok (q 535670832#u32 1416950173#u32 1738206845#u32 1878612285#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1068177915 < 2147483647 ∧ 1187963517 < 2147483647) ∧ (369699898 < 2147483647 ∧ 1881465080 < 2147483647); omega) canonical02 (by rfl)
#print axioms add02
theorem mul01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 535670832#u32 1416950173#u32 1738206845#u32 1878612285#u32) (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32)=ok (q 64768038#u32 627225897#u32 1498929095#u32 1171059667#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (535670832 < 2147483647 ∧ 1416950173 < 2147483647) ∧ (1738206845 < 2147483647 ∧ 1878612285 < 2147483647); omega) (by change (1410683225 < 2147483647 ∧ 375596669 < 2147483647) ∧ (973261870 < 2147483647 ∧ 122086709 < 2147483647); omega) (by rfl)
#print axioms mul01
theorem add01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 64768038#u32 627225897#u32 1498929095#u32 1171059667#u32) c01=ok (q 363945749#u32 1992071884#u32 1478693232#u32 1868667061#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (64768038 < 2147483647 ∧ 627225897 < 2147483647) ∧ (1498929095 < 2147483647 ∧ 1171059667 < 2147483647); omega) canonical01 (by rfl)
#print axioms add01
theorem mul00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 363945749#u32 1992071884#u32 1478693232#u32 1868667061#u32) (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32)=ok (q 103211719#u32 277290460#u32 596951889#u32 2048525258#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (363945749 < 2147483647 ∧ 1992071884 < 2147483647) ∧ (1478693232 < 2147483647 ∧ 1868667061 < 2147483647); omega) (by change (1410683225 < 2147483647 ∧ 375596669 < 2147483647) ∧ (973261870 < 2147483647 ∧ 122086709 < 2147483647); omega) (by rfl)
#print axioms mul00
theorem add00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 103211719#u32 277290460#u32 596951889#u32 2048525258#u32) c00=ok (q 1774972270#u32 814652795#u32 960826620#u32 1189874498#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (103211719 < 2147483647 ∧ 277290460 < 2147483647) ∧ (596951889 < 2147483647 ∧ 2048525258 < 2147483647); omega) canonical00 (by rfl)
#print axioms add00
def final : Q := (q 1774972270#u32 814652795#u32 960826620#u32 1189874498#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 6#usize 14#usize initial 0#usize final := by
  refine .step (by change 14>0; omega) (JFr_IndexArithmetic.sub 14#usize 13#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32) from rfl) mul13 (show Array.index_usize p 13#usize=ok c13 from rfl) add13 ?_
  refine .step (by change 13>0; omega) (JFr_IndexArithmetic.sub 13#usize 12#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32) from rfl) mul12 (show Array.index_usize p 12#usize=ok c12 from rfl) add12 ?_
  refine .step (by change 12>0; omega) (JFr_IndexArithmetic.sub 12#usize 11#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32) from rfl) mul11 (show Array.index_usize p 11#usize=ok c11 from rfl) add11 ?_
  refine .step (by change 11>0; omega) (JFr_IndexArithmetic.sub 11#usize 10#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32) from rfl) mul10 (show Array.index_usize p 10#usize=ok c10 from rfl) add10 ?_
  refine .step (by change 10>0; omega) (JFr_IndexArithmetic.sub 10#usize 9#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32) from rfl) mul09 (show Array.index_usize p 9#usize=ok c09 from rfl) add09 ?_
  refine .step (by change 9>0; omega) (JFr_IndexArithmetic.sub 9#usize 8#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32) from rfl) mul08 (show Array.index_usize p 8#usize=ok c08 from rfl) add08 ?_
  refine .step (by change 8>0; omega) (JFr_IndexArithmetic.sub 8#usize 7#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32) from rfl) mul07 (show Array.index_usize p 7#usize=ok c07 from rfl) add07 ?_
  refine .step (by change 7>0; omega) (JFr_IndexArithmetic.sub 7#usize 6#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32) from rfl) mul06 (show Array.index_usize p 6#usize=ok c06 from rfl) add06 ?_
  refine .step (by change 6>0; omega) (JFr_IndexArithmetic.sub 6#usize 5#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32) from rfl) mul05 (show Array.index_usize p 5#usize=ok c05 from rfl) add05 ?_
  refine .step (by change 5>0; omega) (JFr_IndexArithmetic.sub 5#usize 4#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32) from rfl) mul04 (show Array.index_usize p 4#usize=ok c04 from rfl) add04 ?_
  refine .step (by change 4>0; omega) (JFr_IndexArithmetic.sub 4#usize 3#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32) from rfl) mul03 (show Array.index_usize p 3#usize=ok c03 from rfl) add03 ?_
  refine .step (by change 3>0; omega) (JFr_IndexArithmetic.sub 3#usize 2#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32) from rfl) mul02 (show Array.index_usize p 2#usize=ok c02 from rfl) add02 ?_
  refine .step (by change 2>0; omega) (JFr_IndexArithmetic.sub 2#usize 1#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32) from rfl) mul01 (show Array.index_usize p 1#usize=ok c01 from rfl) add01 ?_
  refine .step (by change 1>0; omega) (JFr_IndexArithmetic.sub 1#usize 0#usize rfl) (show Array.index_usize alpha 6#usize=ok (q 1410683225#u32 375596669#u32 973261870#u32 122086709#u32) from rfl) mul00 (show Array.index_usize p 0#usize=ok c00 from rfl) add00 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner06_1
