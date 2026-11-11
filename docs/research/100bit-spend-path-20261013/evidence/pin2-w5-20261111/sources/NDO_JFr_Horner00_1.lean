import NDO_JFr_Data00
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner00_1
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data00
def initial : Q := (q 484123196#u32 1780186450#u32 1612679921#u32 1127012705#u32)
theorem mul13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 484123196#u32 1780186450#u32 1612679921#u32 1127012705#u32) (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32)=ok (q 1423747734#u32 376858437#u32 221987787#u32 147067284#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (484123196 < 2147483647 ∧ 1780186450 < 2147483647) ∧ (1612679921 < 2147483647 ∧ 1127012705 < 2147483647); omega) (by change (481946492 < 2147483647 ∧ 959095368 < 2147483647) ∧ (2134045306 < 2147483647 ∧ 1739942601 < 2147483647); omega) (by rfl)
#print axioms mul13
theorem add13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1423747734#u32 376858437#u32 221987787#u32 147067284#u32) c13=ok (q 1914834873#u32 1424648496#u32 1191945182#u32 2052382404#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1423747734 < 2147483647 ∧ 376858437 < 2147483647) ∧ (221987787 < 2147483647 ∧ 147067284 < 2147483647); omega) canonical13 (by rfl)
#print axioms add13
theorem mul12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1914834873#u32 1424648496#u32 1191945182#u32 2052382404#u32) (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32)=ok (q 1514021557#u32 491999472#u32 186438981#u32 1497398950#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1914834873 < 2147483647 ∧ 1424648496 < 2147483647) ∧ (1191945182 < 2147483647 ∧ 2052382404 < 2147483647); omega) (by change (481946492 < 2147483647 ∧ 959095368 < 2147483647) ∧ (2134045306 < 2147483647 ∧ 1739942601 < 2147483647); omega) (by rfl)
#print axioms mul12
theorem add12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1514021557#u32 491999472#u32 186438981#u32 1497398950#u32) c12=ok (q 725991178#u32 353679928#u32 1224023258#u32 1938262251#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1514021557 < 2147483647 ∧ 491999472 < 2147483647) ∧ (186438981 < 2147483647 ∧ 1497398950 < 2147483647); omega) canonical12 (by rfl)
#print axioms add12
theorem mul11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 725991178#u32 353679928#u32 1224023258#u32 1938262251#u32) (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32)=ok (q 2097888983#u32 145855735#u32 1945147186#u32 493698838#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (725991178 < 2147483647 ∧ 353679928 < 2147483647) ∧ (1224023258 < 2147483647 ∧ 1938262251 < 2147483647); omega) (by change (481946492 < 2147483647 ∧ 959095368 < 2147483647) ∧ (2134045306 < 2147483647 ∧ 1739942601 < 2147483647); omega) (by rfl)
#print axioms mul11
theorem add11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2097888983#u32 145855735#u32 1945147186#u32 493698838#u32) c11=ok (q 424116890#u32 301806480#u32 273100297#u32 757128675#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2097888983 < 2147483647 ∧ 145855735 < 2147483647) ∧ (1945147186 < 2147483647 ∧ 493698838 < 2147483647); omega) canonical11 (by rfl)
#print axioms add11
theorem mul10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 424116890#u32 301806480#u32 273100297#u32 757128675#u32) (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32)=ok (q 1931959313#u32 1345867206#u32 906594250#u32 1269571079#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (424116890 < 2147483647 ∧ 301806480 < 2147483647) ∧ (273100297 < 2147483647 ∧ 757128675 < 2147483647); omega) (by change (481946492 < 2147483647 ∧ 959095368 < 2147483647) ∧ (2134045306 < 2147483647 ∧ 1739942601 < 2147483647); omega) (by rfl)
#print axioms mul10
theorem add10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1931959313#u32 1345867206#u32 906594250#u32 1269571079#u32) c10=ok (q 1154824542#u32 1170490277#u32 1799388022#u32 1338861724#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1931959313 < 2147483647 ∧ 1345867206 < 2147483647) ∧ (906594250 < 2147483647 ∧ 1269571079 < 2147483647); omega) canonical10 (by rfl)
#print axioms add10
theorem mul09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1154824542#u32 1170490277#u32 1799388022#u32 1338861724#u32) (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32)=ok (q 578741527#u32 1531188929#u32 1678031442#u32 757030381#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1154824542 < 2147483647 ∧ 1170490277 < 2147483647) ∧ (1799388022 < 2147483647 ∧ 1338861724 < 2147483647); omega) (by change (481946492 < 2147483647 ∧ 959095368 < 2147483647) ∧ (2134045306 < 2147483647 ∧ 1739942601 < 2147483647); omega) (by rfl)
#print axioms mul09
theorem add09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 578741527#u32 1531188929#u32 1678031442#u32 757030381#u32) c09=ok (q 1227697497#u32 1004993623#u32 347746187#u32 225935253#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (578741527 < 2147483647 ∧ 1531188929 < 2147483647) ∧ (1678031442 < 2147483647 ∧ 757030381 < 2147483647); omega) canonical09 (by rfl)
#print axioms add09
theorem mul08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1227697497#u32 1004993623#u32 347746187#u32 225935253#u32) (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32)=ok (q 1117532085#u32 2013097792#u32 364600490#u32 13596683#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1227697497 < 2147483647 ∧ 1004993623 < 2147483647) ∧ (347746187 < 2147483647 ∧ 225935253 < 2147483647); omega) (by change (481946492 < 2147483647 ∧ 959095368 < 2147483647) ∧ (2134045306 < 2147483647 ∧ 1739942601 < 2147483647); omega) (by rfl)
#print axioms mul08
theorem add08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1117532085#u32 2013097792#u32 364600490#u32 13596683#u32) c08=ok (q 1222256447#u32 1269236257#u32 1710080724#u32 609020866#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1117532085 < 2147483647 ∧ 2013097792 < 2147483647) ∧ (364600490 < 2147483647 ∧ 13596683 < 2147483647); omega) canonical08 (by rfl)
#print axioms add08
theorem mul07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1222256447#u32 1269236257#u32 1710080724#u32 609020866#u32) (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32)=ok (q 1156262722#u32 536091823#u32 1918525681#u32 651187923#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1222256447 < 2147483647 ∧ 1269236257 < 2147483647) ∧ (1710080724 < 2147483647 ∧ 609020866 < 2147483647); omega) (by change (481946492 < 2147483647 ∧ 959095368 < 2147483647) ∧ (2134045306 < 2147483647 ∧ 1739942601 < 2147483647); omega) (by rfl)
#print axioms mul07
theorem add07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1156262722#u32 536091823#u32 1918525681#u32 651187923#u32) c07=ok (q 1427092240#u32 1153312758#u32 914077946#u32 1384645407#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1156262722 < 2147483647 ∧ 536091823 < 2147483647) ∧ (1918525681 < 2147483647 ∧ 651187923 < 2147483647); omega) canonical07 (by rfl)
#print axioms add07
theorem mul06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1427092240#u32 1153312758#u32 914077946#u32 1384645407#u32) (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32)=ok (q 1764506376#u32 1714676579#u32 643887935#u32 2136218028#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1427092240 < 2147483647 ∧ 1153312758 < 2147483647) ∧ (914077946 < 2147483647 ∧ 1384645407 < 2147483647); omega) (by change (481946492 < 2147483647 ∧ 959095368 < 2147483647) ∧ (2134045306 < 2147483647 ∧ 1739942601 < 2147483647); omega) (by rfl)
#print axioms mul06
theorem add06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1764506376#u32 1714676579#u32 643887935#u32 2136218028#u32) c06=ok (q 2086087500#u32 1158835904#u32 1047055023#u32 1797769690#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1764506376 < 2147483647 ∧ 1714676579 < 2147483647) ∧ (643887935 < 2147483647 ∧ 2136218028 < 2147483647); omega) canonical06 (by rfl)
#print axioms add06
theorem mul05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2086087500#u32 1158835904#u32 1047055023#u32 1797769690#u32) (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32)=ok (q 12986227#u32 1550156325#u32 412256123#u32 955209042#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2086087500 < 2147483647 ∧ 1158835904 < 2147483647) ∧ (1047055023 < 2147483647 ∧ 1797769690 < 2147483647); omega) (by change (481946492 < 2147483647 ∧ 959095368 < 2147483647) ∧ (2134045306 < 2147483647 ∧ 1739942601 < 2147483647); omega) (by rfl)
#print axioms mul05
theorem add05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 12986227#u32 1550156325#u32 412256123#u32 955209042#u32) c05=ok (q 1072885781#u32 1007909553#u32 485264227#u32 1302781103#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (12986227 < 2147483647 ∧ 1550156325 < 2147483647) ∧ (412256123 < 2147483647 ∧ 955209042 < 2147483647); omega) canonical05 (by rfl)
#print axioms add05
theorem mul04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1072885781#u32 1007909553#u32 485264227#u32 1302781103#u32) (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32)=ok (q 290578747#u32 989040413#u32 1259175099#u32 25821268#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1072885781 < 2147483647 ∧ 1007909553 < 2147483647) ∧ (485264227 < 2147483647 ∧ 1302781103 < 2147483647); omega) (by change (481946492 < 2147483647 ∧ 959095368 < 2147483647) ∧ (2134045306 < 2147483647 ∧ 1739942601 < 2147483647); omega) (by rfl)
#print axioms mul04
theorem add04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 290578747#u32 989040413#u32 1259175099#u32 25821268#u32) c04=ok (q 1607222983#u32 494234336#u32 1167485278#u32 1948379306#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (290578747 < 2147483647 ∧ 989040413 < 2147483647) ∧ (1259175099 < 2147483647 ∧ 25821268 < 2147483647); omega) canonical04 (by rfl)
#print axioms add04
theorem mul03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1607222983#u32 494234336#u32 1167485278#u32 1948379306#u32) (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32)=ok (q 2021342006#u32 524167431#u32 289162254#u32 694954312#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1607222983 < 2147483647 ∧ 494234336 < 2147483647) ∧ (1167485278 < 2147483647 ∧ 1948379306 < 2147483647); omega) (by change (481946492 < 2147483647 ∧ 959095368 < 2147483647) ∧ (2134045306 < 2147483647 ∧ 1739942601 < 2147483647); omega) (by rfl)
#print axioms mul03
theorem add03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2021342006#u32 524167431#u32 289162254#u32 694954312#u32) c03=ok (q 1149200987#u32 2046915586#u32 2076707923#u32 237761194#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2021342006 < 2147483647 ∧ 524167431 < 2147483647) ∧ (289162254 < 2147483647 ∧ 694954312 < 2147483647); omega) canonical03 (by rfl)
#print axioms add03
theorem mul02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1149200987#u32 2046915586#u32 2076707923#u32 237761194#u32) (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32)=ok (q 556310401#u32 1489202758#u32 1585314855#u32 32641670#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1149200987 < 2147483647 ∧ 2046915586 < 2147483647) ∧ (2076707923 < 2147483647 ∧ 237761194 < 2147483647); omega) (by change (481946492 < 2147483647 ∧ 959095368 < 2147483647) ∧ (2134045306 < 2147483647 ∧ 1739942601 < 2147483647); omega) (by rfl)
#print axioms mul02
theorem add02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 556310401#u32 1489202758#u32 1585314855#u32 32641670#u32) c02=ok (q 740032660#u32 2006401070#u32 1457742824#u32 889289581#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (556310401 < 2147483647 ∧ 1489202758 < 2147483647) ∧ (1585314855 < 2147483647 ∧ 32641670 < 2147483647); omega) canonical02 (by rfl)
#print axioms add02
theorem mul01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 740032660#u32 2006401070#u32 1457742824#u32 889289581#u32) (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32)=ok (q 1199928184#u32 772142794#u32 1825582492#u32 1474874179#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (740032660 < 2147483647 ∧ 2006401070 < 2147483647) ∧ (1457742824 < 2147483647 ∧ 889289581 < 2147483647); omega) (by change (481946492 < 2147483647 ∧ 959095368 < 2147483647) ∧ (2134045306 < 2147483647 ∧ 1739942601 < 2147483647); omega) (by rfl)
#print axioms mul01
theorem add01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1199928184#u32 772142794#u32 1825582492#u32 1474874179#u32) c01=ok (q 564751410#u32 1626376985#u32 341662729#u32 2109111505#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1199928184 < 2147483647 ∧ 772142794 < 2147483647) ∧ (1825582492 < 2147483647 ∧ 1474874179 < 2147483647); omega) canonical01 (by rfl)
#print axioms add01
theorem mul00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 564751410#u32 1626376985#u32 341662729#u32 2109111505#u32) (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32)=ok (q 248700735#u32 1916487488#u32 1503143376#u32 1544790538#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (564751410 < 2147483647 ∧ 1626376985 < 2147483647) ∧ (341662729 < 2147483647 ∧ 2109111505 < 2147483647); omega) (by change (481946492 < 2147483647 ∧ 959095368 < 2147483647) ∧ (2134045306 < 2147483647 ∧ 1739942601 < 2147483647); omega) (by rfl)
#print axioms mul00
theorem add00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 248700735#u32 1916487488#u32 1503143376#u32 1544790538#u32) c00=ok (q 1639703056#u32 1424909894#u32 380442273#u32 581392954#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (248700735 < 2147483647 ∧ 1916487488 < 2147483647) ∧ (1503143376 < 2147483647 ∧ 1544790538 < 2147483647); omega) canonical00 (by rfl)
#print axioms add00
def final : Q := (q 1639703056#u32 1424909894#u32 380442273#u32 581392954#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 0#usize 14#usize initial 0#usize final := by
  refine .step (by change 14>0; omega) (JFr_IndexArithmetic.sub 14#usize 13#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32) from rfl) mul13 (show Array.index_usize p 13#usize=ok c13 from rfl) add13 ?_
  refine .step (by change 13>0; omega) (JFr_IndexArithmetic.sub 13#usize 12#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32) from rfl) mul12 (show Array.index_usize p 12#usize=ok c12 from rfl) add12 ?_
  refine .step (by change 12>0; omega) (JFr_IndexArithmetic.sub 12#usize 11#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32) from rfl) mul11 (show Array.index_usize p 11#usize=ok c11 from rfl) add11 ?_
  refine .step (by change 11>0; omega) (JFr_IndexArithmetic.sub 11#usize 10#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32) from rfl) mul10 (show Array.index_usize p 10#usize=ok c10 from rfl) add10 ?_
  refine .step (by change 10>0; omega) (JFr_IndexArithmetic.sub 10#usize 9#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32) from rfl) mul09 (show Array.index_usize p 9#usize=ok c09 from rfl) add09 ?_
  refine .step (by change 9>0; omega) (JFr_IndexArithmetic.sub 9#usize 8#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32) from rfl) mul08 (show Array.index_usize p 8#usize=ok c08 from rfl) add08 ?_
  refine .step (by change 8>0; omega) (JFr_IndexArithmetic.sub 8#usize 7#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32) from rfl) mul07 (show Array.index_usize p 7#usize=ok c07 from rfl) add07 ?_
  refine .step (by change 7>0; omega) (JFr_IndexArithmetic.sub 7#usize 6#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32) from rfl) mul06 (show Array.index_usize p 6#usize=ok c06 from rfl) add06 ?_
  refine .step (by change 6>0; omega) (JFr_IndexArithmetic.sub 6#usize 5#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32) from rfl) mul05 (show Array.index_usize p 5#usize=ok c05 from rfl) add05 ?_
  refine .step (by change 5>0; omega) (JFr_IndexArithmetic.sub 5#usize 4#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32) from rfl) mul04 (show Array.index_usize p 4#usize=ok c04 from rfl) add04 ?_
  refine .step (by change 4>0; omega) (JFr_IndexArithmetic.sub 4#usize 3#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32) from rfl) mul03 (show Array.index_usize p 3#usize=ok c03 from rfl) add03 ?_
  refine .step (by change 3>0; omega) (JFr_IndexArithmetic.sub 3#usize 2#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32) from rfl) mul02 (show Array.index_usize p 2#usize=ok c02 from rfl) add02 ?_
  refine .step (by change 2>0; omega) (JFr_IndexArithmetic.sub 2#usize 1#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32) from rfl) mul01 (show Array.index_usize p 1#usize=ok c01 from rfl) add01 ?_
  refine .step (by change 1>0; omega) (JFr_IndexArithmetic.sub 1#usize 0#usize rfl) (show Array.index_usize alpha 0#usize=ok (q 481946492#u32 959095368#u32 2134045306#u32 1739942601#u32) from rfl) mul00 (show Array.index_usize p 0#usize=ok c00 from rfl) add00 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner00_1
