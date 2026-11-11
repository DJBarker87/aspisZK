import NDO_JFr_Data08
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner08_1
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data08
def initial : Q := (q 2112930430#u32 1994933690#u32 877632083#u32 1341230312#u32)
theorem mul13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2112930430#u32 1994933690#u32 877632083#u32 1341230312#u32) (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32)=ok (q 2033414659#u32 1656602263#u32 1163551239#u32 45267712#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2112930430 < 2147483647 ∧ 1994933690 < 2147483647) ∧ (877632083 < 2147483647 ∧ 1341230312 < 2147483647); omega) (by change (124721160 < 2147483647 ∧ 1463026064 < 2147483647) ∧ (316880895 < 2147483647 ∧ 1559203092 < 2147483647); omega) (by rfl)
#print axioms mul13
theorem add13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2033414659#u32 1656602263#u32 1163551239#u32 45267712#u32) c13=ok (q 1872715846#u32 363356256#u32 663366174#u32 96978543#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2033414659 < 2147483647 ∧ 1656602263 < 2147483647) ∧ (1163551239 < 2147483647 ∧ 45267712 < 2147483647); omega) canonical13 (by rfl)
#print axioms add13
theorem mul12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1872715846#u32 363356256#u32 663366174#u32 96978543#u32) (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32)=ok (q 2024164574#u32 68422821#u32 72637094#u32 1909955404#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1872715846 < 2147483647 ∧ 363356256 < 2147483647) ∧ (663366174 < 2147483647 ∧ 96978543 < 2147483647); omega) (by change (124721160 < 2147483647 ∧ 1463026064 < 2147483647) ∧ (316880895 < 2147483647 ∧ 1559203092 < 2147483647); omega) (by rfl)
#print axioms mul12
theorem add12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2024164574#u32 68422821#u32 72637094#u32 1909955404#u32) c12=ok (q 1198957044#u32 1896312438#u32 1068663659#u32 2069116697#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2024164574 < 2147483647 ∧ 68422821 < 2147483647) ∧ (72637094 < 2147483647 ∧ 1909955404 < 2147483647); omega) canonical12 (by rfl)
#print axioms add12
theorem mul11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1198957044#u32 1896312438#u32 1068663659#u32 2069116697#u32) (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32)=ok (q 1153069870#u32 613539880#u32 562464887#u32 477389627#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1198957044 < 2147483647 ∧ 1896312438 < 2147483647) ∧ (1068663659 < 2147483647 ∧ 2069116697 < 2147483647); omega) (by change (124721160 < 2147483647 ∧ 1463026064 < 2147483647) ∧ (316880895 < 2147483647 ∧ 1559203092 < 2147483647); omega) (by rfl)
#print axioms mul11
theorem add11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1153069870#u32 613539880#u32 562464887#u32 477389627#u32) c11=ok (q 1739109288#u32 998915808#u32 220666129#u32 1723879018#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1153069870 < 2147483647 ∧ 613539880 < 2147483647) ∧ (562464887 < 2147483647 ∧ 477389627 < 2147483647); omega) canonical11 (by rfl)
#print axioms add11
theorem mul10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1739109288#u32 998915808#u32 220666129#u32 1723879018#u32) (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32)=ok (q 1932832236#u32 358734695#u32 651208618#u32 312991741#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1739109288 < 2147483647 ∧ 998915808 < 2147483647) ∧ (220666129 < 2147483647 ∧ 1723879018 < 2147483647); omega) (by change (124721160 < 2147483647 ∧ 1463026064 < 2147483647) ∧ (316880895 < 2147483647 ∧ 1559203092 < 2147483647); omega) (by rfl)
#print axioms mul10
theorem add10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1932832236#u32 358734695#u32 651208618#u32 312991741#u32) c10=ok (q 1736022744#u32 830395753#u32 934990027#u32 213989311#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1932832236 < 2147483647 ∧ 358734695 < 2147483647) ∧ (651208618 < 2147483647 ∧ 312991741 < 2147483647); omega) canonical10 (by rfl)
#print axioms add10
theorem mul09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1736022744#u32 830395753#u32 934990027#u32 213989311#u32) (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32)=ok (q 1041608758#u32 1578216471#u32 269461796#u32 1175918875#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1736022744 < 2147483647 ∧ 830395753 < 2147483647) ∧ (934990027 < 2147483647 ∧ 213989311 < 2147483647); omega) (by change (124721160 < 2147483647 ∧ 1463026064 < 2147483647) ∧ (316880895 < 2147483647 ∧ 1559203092 < 2147483647); omega) (by rfl)
#print axioms mul09
theorem add09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1041608758#u32 1578216471#u32 269461796#u32 1175918875#u32) c09=ok (q 1314209360#u32 2048042415#u32 1850006074#u32 777301#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1041608758 < 2147483647 ∧ 1578216471 < 2147483647) ∧ (269461796 < 2147483647 ∧ 1175918875 < 2147483647); omega) canonical09 (by rfl)
#print axioms add09
theorem mul08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1314209360#u32 2048042415#u32 1850006074#u32 777301#u32) (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32)=ok (q 378788209#u32 1728378761#u32 1969716105#u32 893771750#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1314209360 < 2147483647 ∧ 2048042415 < 2147483647) ∧ (1850006074 < 2147483647 ∧ 777301 < 2147483647); omega) (by change (124721160 < 2147483647 ∧ 1463026064 < 2147483647) ∧ (316880895 < 2147483647 ∧ 1559203092 < 2147483647); omega) (by rfl)
#print axioms mul08
theorem add08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 378788209#u32 1728378761#u32 1969716105#u32 893771750#u32) c08=ok (q 1037679326#u32 679333287#u32 460900141#u32 552002442#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (378788209 < 2147483647 ∧ 1728378761 < 2147483647) ∧ (1969716105 < 2147483647 ∧ 893771750 < 2147483647); omega) canonical08 (by rfl)
#print axioms add08
theorem mul07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1037679326#u32 679333287#u32 460900141#u32 552002442#u32) (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32)=ok (q 1373059112#u32 968962348#u32 1357975276#u32 58989748#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1037679326 < 2147483647 ∧ 679333287 < 2147483647) ∧ (460900141 < 2147483647 ∧ 552002442 < 2147483647); omega) (by change (124721160 < 2147483647 ∧ 1463026064 < 2147483647) ∧ (316880895 < 2147483647 ∧ 1559203092 < 2147483647); omega) (by rfl)
#print axioms mul07
theorem add07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1373059112#u32 968962348#u32 1357975276#u32 58989748#u32) c07=ok (q 1141085693#u32 1746752433#u32 160328871#u32 1268559924#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1373059112 < 2147483647 ∧ 968962348 < 2147483647) ∧ (1357975276 < 2147483647 ∧ 58989748 < 2147483647); omega) canonical07 (by rfl)
#print axioms add07
theorem mul06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1141085693#u32 1746752433#u32 160328871#u32 1268559924#u32) (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32)=ok (q 1812469955#u32 1457749934#u32 178627480#u32 1414351862#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1141085693 < 2147483647 ∧ 1746752433 < 2147483647) ∧ (160328871 < 2147483647 ∧ 1268559924 < 2147483647); omega) (by change (124721160 < 2147483647 ∧ 1463026064 < 2147483647) ∧ (316880895 < 2147483647 ∧ 1559203092 < 2147483647); omega) (by rfl)
#print axioms mul06
theorem add06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1812469955#u32 1457749934#u32 178627480#u32 1414351862#u32) c06=ok (q 427527891#u32 8169670#u32 1519317388#u32 134340243#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1812469955 < 2147483647 ∧ 1457749934 < 2147483647) ∧ (178627480 < 2147483647 ∧ 1414351862 < 2147483647); omega) canonical06 (by rfl)
#print axioms add06
theorem mul05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 427527891#u32 8169670#u32 1519317388#u32 134340243#u32) (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32)=ok (q 771897937#u32 60644163#u32 495861805#u32 1987973932#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (427527891 < 2147483647 ∧ 8169670 < 2147483647) ∧ (1519317388 < 2147483647 ∧ 134340243 < 2147483647); omega) (by change (124721160 < 2147483647 ∧ 1463026064 < 2147483647) ∧ (316880895 < 2147483647 ∧ 1559203092 < 2147483647); omega) (by rfl)
#print axioms mul05
theorem add05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 771897937#u32 60644163#u32 495861805#u32 1987973932#u32) c05=ok (q 2098128610#u32 438960521#u32 1229828827#u32 932501663#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (771897937 < 2147483647 ∧ 60644163 < 2147483647) ∧ (495861805 < 2147483647 ∧ 1987973932 < 2147483647); omega) canonical05 (by rfl)
#print axioms add05
theorem mul04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2098128610#u32 438960521#u32 1229828827#u32 932501663#u32) (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32)=ok (q 117606566#u32 408857220#u32 603105687#u32 697807470#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2098128610 < 2147483647 ∧ 438960521 < 2147483647) ∧ (1229828827 < 2147483647 ∧ 932501663 < 2147483647); omega) (by change (124721160 < 2147483647 ∧ 1463026064 < 2147483647) ∧ (316880895 < 2147483647 ∧ 1559203092 < 2147483647); omega) (by rfl)
#print axioms mul04
theorem add04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 117606566#u32 408857220#u32 603105687#u32 697807470#u32) c04=ok (q 1156173671#u32 1342328313#u32 189340615#u32 1915936675#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (117606566 < 2147483647 ∧ 408857220 < 2147483647) ∧ (603105687 < 2147483647 ∧ 697807470 < 2147483647); omega) canonical04 (by rfl)
#print axioms add04
theorem mul03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1156173671#u32 1342328313#u32 189340615#u32 1915936675#u32) (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32)=ok (q 1727603098#u32 319798038#u32 750007827#u32 478957890#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1156173671 < 2147483647 ∧ 1342328313 < 2147483647) ∧ (189340615 < 2147483647 ∧ 1915936675 < 2147483647); omega) (by change (124721160 < 2147483647 ∧ 1463026064 < 2147483647) ∧ (316880895 < 2147483647 ∧ 1559203092 < 2147483647); omega) (by rfl)
#print axioms mul03
theorem add03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1727603098#u32 319798038#u32 750007827#u32 478957890#u32) c03=ok (q 295930665#u32 90772102#u32 302028586#u32 1852395728#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1727603098 < 2147483647 ∧ 319798038 < 2147483647) ∧ (750007827 < 2147483647 ∧ 478957890 < 2147483647); omega) canonical03 (by rfl)
#print axioms add03
theorem mul02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 295930665#u32 90772102#u32 302028586#u32 1852395728#u32) (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32)=ok (q 1997190014#u32 1532682234#u32 582840738#u32 871638944#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (295930665 < 2147483647 ∧ 90772102 < 2147483647) ∧ (302028586 < 2147483647 ∧ 1852395728 < 2147483647); omega) (by change (124721160 < 2147483647 ∧ 1463026064 < 2147483647) ∧ (316880895 < 2147483647 ∧ 1559203092 < 2147483647); omega) (by rfl)
#print axioms mul02
theorem add02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1997190014#u32 1532682234#u32 582840738#u32 871638944#u32) c02=ok (q 966881053#u32 1391462929#u32 170300888#u32 1481652237#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1997190014 < 2147483647 ∧ 1532682234 < 2147483647) ∧ (582840738 < 2147483647 ∧ 871638944 < 2147483647); omega) canonical02 (by rfl)
#print axioms add02
theorem mul01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 966881053#u32 1391462929#u32 170300888#u32 1481652237#u32) (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32)=ok (q 365864619#u32 527536559#u32 182182675#u32 1206497322#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (966881053 < 2147483647 ∧ 1391462929 < 2147483647) ∧ (170300888 < 2147483647 ∧ 1481652237 < 2147483647); omega) (by change (124721160 < 2147483647 ∧ 1463026064 < 2147483647) ∧ (316880895 < 2147483647 ∧ 1559203092 < 2147483647); omega) (by rfl)
#print axioms mul01
theorem add01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 365864619#u32 527536559#u32 182182675#u32 1206497322#u32) c01=ok (q 283400499#u32 150555448#u32 2077118346#u32 449212744#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (365864619 < 2147483647 ∧ 527536559 < 2147483647) ∧ (182182675 < 2147483647 ∧ 1206497322 < 2147483647); omega) canonical01 (by rfl)
#print axioms add01
theorem mul00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 283400499#u32 150555448#u32 2077118346#u32 449212744#u32) (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32)=ok (q 75102960#u32 920832372#u32 1319214147#u32 1050930700#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (283400499 < 2147483647 ∧ 150555448 < 2147483647) ∧ (2077118346 < 2147483647 ∧ 449212744 < 2147483647); omega) (by change (124721160 < 2147483647 ∧ 1463026064 < 2147483647) ∧ (316880895 < 2147483647 ∧ 1559203092 < 2147483647); omega) (by rfl)
#print axioms mul00
theorem add00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 75102960#u32 920832372#u32 1319214147#u32 1050930700#u32) c00=ok (q 1134233061#u32 1799343102#u32 366950497#u32 1208920298#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (75102960 < 2147483647 ∧ 920832372 < 2147483647) ∧ (1319214147 < 2147483647 ∧ 1050930700 < 2147483647); omega) canonical00 (by rfl)
#print axioms add00
def final : Q := (q 1134233061#u32 1799343102#u32 366950497#u32 1208920298#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 8#usize 14#usize initial 0#usize final := by
  refine .step (by change 14>0; omega) (JFr_IndexArithmetic.sub 14#usize 13#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32) from rfl) mul13 (show Array.index_usize p 13#usize=ok c13 from rfl) add13 ?_
  refine .step (by change 13>0; omega) (JFr_IndexArithmetic.sub 13#usize 12#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32) from rfl) mul12 (show Array.index_usize p 12#usize=ok c12 from rfl) add12 ?_
  refine .step (by change 12>0; omega) (JFr_IndexArithmetic.sub 12#usize 11#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32) from rfl) mul11 (show Array.index_usize p 11#usize=ok c11 from rfl) add11 ?_
  refine .step (by change 11>0; omega) (JFr_IndexArithmetic.sub 11#usize 10#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32) from rfl) mul10 (show Array.index_usize p 10#usize=ok c10 from rfl) add10 ?_
  refine .step (by change 10>0; omega) (JFr_IndexArithmetic.sub 10#usize 9#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32) from rfl) mul09 (show Array.index_usize p 9#usize=ok c09 from rfl) add09 ?_
  refine .step (by change 9>0; omega) (JFr_IndexArithmetic.sub 9#usize 8#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32) from rfl) mul08 (show Array.index_usize p 8#usize=ok c08 from rfl) add08 ?_
  refine .step (by change 8>0; omega) (JFr_IndexArithmetic.sub 8#usize 7#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32) from rfl) mul07 (show Array.index_usize p 7#usize=ok c07 from rfl) add07 ?_
  refine .step (by change 7>0; omega) (JFr_IndexArithmetic.sub 7#usize 6#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32) from rfl) mul06 (show Array.index_usize p 6#usize=ok c06 from rfl) add06 ?_
  refine .step (by change 6>0; omega) (JFr_IndexArithmetic.sub 6#usize 5#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32) from rfl) mul05 (show Array.index_usize p 5#usize=ok c05 from rfl) add05 ?_
  refine .step (by change 5>0; omega) (JFr_IndexArithmetic.sub 5#usize 4#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32) from rfl) mul04 (show Array.index_usize p 4#usize=ok c04 from rfl) add04 ?_
  refine .step (by change 4>0; omega) (JFr_IndexArithmetic.sub 4#usize 3#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32) from rfl) mul03 (show Array.index_usize p 3#usize=ok c03 from rfl) add03 ?_
  refine .step (by change 3>0; omega) (JFr_IndexArithmetic.sub 3#usize 2#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32) from rfl) mul02 (show Array.index_usize p 2#usize=ok c02 from rfl) add02 ?_
  refine .step (by change 2>0; omega) (JFr_IndexArithmetic.sub 2#usize 1#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32) from rfl) mul01 (show Array.index_usize p 1#usize=ok c01 from rfl) add01 ?_
  refine .step (by change 1>0; omega) (JFr_IndexArithmetic.sub 1#usize 0#usize rfl) (show Array.index_usize alpha 8#usize=ok (q 124721160#u32 1463026064#u32 316880895#u32 1559203092#u32) from rfl) mul00 (show Array.index_usize p 0#usize=ok c00 from rfl) add00 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner08_1
