import NDO_JFr_Data03
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner03_0
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data03
def initial : Q := (q 0#u32 0#u32 0#u32 0#u32)
theorem mul27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 0#u32 0#u32 0#u32 0#u32) (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32)=ok (q 0#u32 0#u32 0#u32 0#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) (by change (1777472067 < 2147483647 ∧ 823612886 < 2147483647) ∧ (769288371 < 2147483647 ∧ 68548007 < 2147483647); omega) (by rfl)
#print axioms mul27
theorem add27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 0#u32 0#u32 0#u32 0#u32) c27=ok (q 1692707105#u32 1149629855#u32 1859079306#u32 1623589692#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) canonical27 (by rfl)
#print axioms add27
theorem mul26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1692707105#u32 1149629855#u32 1859079306#u32 1623589692#u32) (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32)=ok (q 275489493#u32 788866820#u32 802825570#u32 1037146223#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1692707105 < 2147483647 ∧ 1149629855 < 2147483647) ∧ (1859079306 < 2147483647 ∧ 1623589692 < 2147483647); omega) (by change (1777472067 < 2147483647 ∧ 823612886 < 2147483647) ∧ (769288371 < 2147483647 ∧ 68548007 < 2147483647); omega) (by rfl)
#print axioms mul26
theorem add26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 275489493#u32 788866820#u32 802825570#u32 1037146223#u32) c26=ok (q 1729117156#u32 1096681093#u32 923158973#u32 9514521#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (275489493 < 2147483647 ∧ 788866820 < 2147483647) ∧ (802825570 < 2147483647 ∧ 1037146223 < 2147483647); omega) canonical26 (by rfl)
#print axioms add26
theorem mul25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1729117156#u32 1096681093#u32 923158973#u32 9514521#u32) (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32)=ok (q 1729430637#u32 1708092216#u32 1175956292#u32 1461810976#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1729117156 < 2147483647 ∧ 1096681093 < 2147483647) ∧ (923158973 < 2147483647 ∧ 9514521 < 2147483647); omega) (by change (1777472067 < 2147483647 ∧ 823612886 < 2147483647) ∧ (769288371 < 2147483647 ∧ 68548007 < 2147483647); omega) (by rfl)
#print axioms mul25
theorem add25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1729430637#u32 1708092216#u32 1175956292#u32 1461810976#u32) c25=ok (q 204022614#u32 1831160038#u32 151751486#u32 681001181#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1729430637 < 2147483647 ∧ 1708092216 < 2147483647) ∧ (1175956292 < 2147483647 ∧ 1461810976 < 2147483647); omega) canonical25 (by rfl)
#print axioms add25
theorem mul24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 204022614#u32 1831160038#u32 151751486#u32 681001181#u32) (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32)=ok (q 431487401#u32 1588536793#u32 1690813761#u32 1313989528#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (204022614 < 2147483647 ∧ 1831160038 < 2147483647) ∧ (151751486 < 2147483647 ∧ 681001181 < 2147483647); omega) (by change (1777472067 < 2147483647 ∧ 823612886 < 2147483647) ∧ (769288371 < 2147483647 ∧ 68548007 < 2147483647); omega) (by rfl)
#print axioms mul24
theorem add24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 431487401#u32 1588536793#u32 1690813761#u32 1313989528#u32) c24=ok (q 2010221654#u32 606902084#u32 1337368531#u32 744707852#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (431487401 < 2147483647 ∧ 1588536793 < 2147483647) ∧ (1690813761 < 2147483647 ∧ 1313989528 < 2147483647); omega) canonical24 (by rfl)
#print axioms add24
theorem mul23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2010221654#u32 606902084#u32 1337368531#u32 744707852#u32) (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32)=ok (q 260112552#u32 991425545#u32 1132932747#u32 1691806363#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2010221654 < 2147483647 ∧ 606902084 < 2147483647) ∧ (1337368531 < 2147483647 ∧ 744707852 < 2147483647); omega) (by change (1777472067 < 2147483647 ∧ 823612886 < 2147483647) ∧ (769288371 < 2147483647 ∧ 68548007 < 2147483647); omega) (by rfl)
#print axioms mul23
theorem add23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 260112552#u32 991425545#u32 1132932747#u32 1691806363#u32) c23=ok (q 215378270#u32 1392890951#u32 154553411#u32 869147503#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (260112552 < 2147483647 ∧ 991425545 < 2147483647) ∧ (1132932747 < 2147483647 ∧ 1691806363 < 2147483647); omega) canonical23 (by rfl)
#print axioms add23
theorem mul22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 215378270#u32 1392890951#u32 154553411#u32 869147503#u32) (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32)=ok (q 116485253#u32 480673523#u32 646715425#u32 568078826#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (215378270 < 2147483647 ∧ 1392890951 < 2147483647) ∧ (154553411 < 2147483647 ∧ 869147503 < 2147483647); omega) (by change (1777472067 < 2147483647 ∧ 823612886 < 2147483647) ∧ (769288371 < 2147483647 ∧ 68548007 < 2147483647); omega) (by rfl)
#print axioms mul22
theorem add22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 116485253#u32 480673523#u32 646715425#u32 568078826#u32) c22=ok (q 2003673660#u32 1576935663#u32 1737884758#u32 1128295277#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (116485253 < 2147483647 ∧ 480673523 < 2147483647) ∧ (646715425 < 2147483647 ∧ 568078826 < 2147483647); omega) canonical22 (by rfl)
#print axioms add22
theorem mul21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2003673660#u32 1576935663#u32 1737884758#u32 1128295277#u32) (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32)=ok (q 1307955003#u32 1111963644#u32 352916975#u32 1093816524#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2003673660 < 2147483647 ∧ 1576935663 < 2147483647) ∧ (1737884758 < 2147483647 ∧ 1128295277 < 2147483647); omega) (by change (1777472067 < 2147483647 ∧ 823612886 < 2147483647) ∧ (769288371 < 2147483647 ∧ 68548007 < 2147483647); omega) (by rfl)
#print axioms mul21
theorem add21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1307955003#u32 1111963644#u32 352916975#u32 1093816524#u32) c21=ok (q 1632150850#u32 2113170500#u32 1999401069#u32 1837902712#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1307955003 < 2147483647 ∧ 1111963644 < 2147483647) ∧ (352916975 < 2147483647 ∧ 1093816524 < 2147483647); omega) canonical21 (by rfl)
#print axioms add21
theorem mul20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1632150850#u32 2113170500#u32 1999401069#u32 1837902712#u32) (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32)=ok (q 187629134#u32 1202755261#u32 2082672421#u32 2093939845#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1632150850 < 2147483647 ∧ 2113170500 < 2147483647) ∧ (1999401069 < 2147483647 ∧ 1837902712 < 2147483647); omega) (by change (1777472067 < 2147483647 ∧ 823612886 < 2147483647) ∧ (769288371 < 2147483647 ∧ 68548007 < 2147483647); omega) (by rfl)
#print axioms mul20
theorem add20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 187629134#u32 1202755261#u32 2082672421#u32 2093939845#u32) c20=ok (q 281285931#u32 1498829842#u32 897043378#u32 189221140#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (187629134 < 2147483647 ∧ 1202755261 < 2147483647) ∧ (2082672421 < 2147483647 ∧ 2093939845 < 2147483647); omega) canonical20 (by rfl)
#print axioms add20
theorem mul19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 281285931#u32 1498829842#u32 897043378#u32 189221140#u32) (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32)=ok (q 1039865176#u32 545429618#u32 208788460#u32 560212998#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (281285931 < 2147483647 ∧ 1498829842 < 2147483647) ∧ (897043378 < 2147483647 ∧ 189221140 < 2147483647); omega) (by change (1777472067 < 2147483647 ∧ 823612886 < 2147483647) ∧ (769288371 < 2147483647 ∧ 68548007 < 2147483647); omega) (by rfl)
#print axioms mul19
theorem add19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1039865176#u32 545429618#u32 208788460#u32 560212998#u32) c19=ok (q 1036701579#u32 9580547#u32 1021040507#u32 1280773847#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1039865176 < 2147483647 ∧ 545429618 < 2147483647) ∧ (208788460 < 2147483647 ∧ 560212998 < 2147483647); omega) canonical19 (by rfl)
#print axioms add19
theorem mul18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1036701579#u32 9580547#u32 1021040507#u32 1280773847#u32) (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32)=ok (q 738981412#u32 928002512#u32 2132142234#u32 1002472959#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1036701579 < 2147483647 ∧ 9580547 < 2147483647) ∧ (1021040507 < 2147483647 ∧ 1280773847 < 2147483647); omega) (by change (1777472067 < 2147483647 ∧ 823612886 < 2147483647) ∧ (769288371 < 2147483647 ∧ 68548007 < 2147483647); omega) (by rfl)
#print axioms mul18
theorem add18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 738981412#u32 928002512#u32 2132142234#u32 1002472959#u32) c18=ok (q 791316077#u32 444482098#u32 2027326601#u32 1009598841#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (738981412 < 2147483647 ∧ 928002512 < 2147483647) ∧ (2132142234 < 2147483647 ∧ 1002472959 < 2147483647); omega) canonical18 (by rfl)
#print axioms add18
theorem mul17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 791316077#u32 444482098#u32 2027326601#u32 1009598841#u32) (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32)=ok (q 925410982#u32 449101788#u32 1299180172#u32 610423340#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (791316077 < 2147483647 ∧ 444482098 < 2147483647) ∧ (2027326601 < 2147483647 ∧ 1009598841 < 2147483647); omega) (by change (1777472067 < 2147483647 ∧ 823612886 < 2147483647) ∧ (769288371 < 2147483647 ∧ 68548007 < 2147483647); omega) (by rfl)
#print axioms mul17
theorem add17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 925410982#u32 449101788#u32 1299180172#u32 610423340#u32) c17=ok (q 977207290#u32 1077108592#u32 927067674#u32 1374886416#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (925410982 < 2147483647 ∧ 449101788 < 2147483647) ∧ (1299180172 < 2147483647 ∧ 610423340 < 2147483647); omega) canonical17 (by rfl)
#print axioms add17
theorem mul16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 977207290#u32 1077108592#u32 927067674#u32 1374886416#u32) (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32)=ok (q 1727947425#u32 764819090#u32 2001249463#u32 211705789#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (977207290 < 2147483647 ∧ 1077108592 < 2147483647) ∧ (927067674 < 2147483647 ∧ 1374886416 < 2147483647); omega) (by change (1777472067 < 2147483647 ∧ 823612886 < 2147483647) ∧ (769288371 < 2147483647 ∧ 68548007 < 2147483647); omega) (by rfl)
#print axioms mul16
theorem add16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1727947425#u32 764819090#u32 2001249463#u32 211705789#u32) c16=ok (q 67539727#u32 894330276#u32 1617759885#u32 2076825004#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1727947425 < 2147483647 ∧ 764819090 < 2147483647) ∧ (2001249463 < 2147483647 ∧ 211705789 < 2147483647); omega) canonical16 (by rfl)
#print axioms add16
theorem mul15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 67539727#u32 894330276#u32 1617759885#u32 2076825004#u32) (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32)=ok (q 835134069#u32 880927780#u32 655244103#u32 315319542#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (67539727 < 2147483647 ∧ 894330276 < 2147483647) ∧ (1617759885 < 2147483647 ∧ 2076825004 < 2147483647); omega) (by change (1777472067 < 2147483647 ∧ 823612886 < 2147483647) ∧ (769288371 < 2147483647 ∧ 68548007 < 2147483647); omega) (by rfl)
#print axioms mul15
theorem add15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 835134069#u32 880927780#u32 655244103#u32 315319542#u32) c15=ok (q 1553656910#u32 1900843647#u32 1532361391#u32 1743196520#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (835134069 < 2147483647 ∧ 880927780 < 2147483647) ∧ (655244103 < 2147483647 ∧ 315319542 < 2147483647); omega) canonical15 (by rfl)
#print axioms add15
theorem mul14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1553656910#u32 1900843647#u32 1532361391#u32 1743196520#u32) (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32)=ok (q 1799466113#u32 830611556#u32 1472341764#u32 1262153968#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1553656910 < 2147483647 ∧ 1900843647 < 2147483647) ∧ (1532361391 < 2147483647 ∧ 1743196520 < 2147483647); omega) (by change (1777472067 < 2147483647 ∧ 823612886 < 2147483647) ∧ (769288371 < 2147483647 ∧ 68548007 < 2147483647); omega) (by rfl)
#print axioms mul14
theorem add14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1799466113#u32 830611556#u32 1472341764#u32 1262153968#u32) c14=ok (q 2094914637#u32 1725791557#u32 1511076010#u32 2070155558#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1799466113 < 2147483647 ∧ 830611556 < 2147483647) ∧ (1472341764 < 2147483647 ∧ 1262153968 < 2147483647); omega) canonical14 (by rfl)
#print axioms add14
def final : Q := (q 2094914637#u32 1725791557#u32 1511076010#u32 2070155558#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 3#usize 28#usize initial 14#usize final := by
  refine .step (by change 28>0; omega) (JFr_IndexArithmetic.sub 28#usize 27#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32) from rfl) mul27 (show Array.index_usize p 27#usize=ok c27 from rfl) add27 ?_
  refine .step (by change 27>0; omega) (JFr_IndexArithmetic.sub 27#usize 26#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32) from rfl) mul26 (show Array.index_usize p 26#usize=ok c26 from rfl) add26 ?_
  refine .step (by change 26>0; omega) (JFr_IndexArithmetic.sub 26#usize 25#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32) from rfl) mul25 (show Array.index_usize p 25#usize=ok c25 from rfl) add25 ?_
  refine .step (by change 25>0; omega) (JFr_IndexArithmetic.sub 25#usize 24#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32) from rfl) mul24 (show Array.index_usize p 24#usize=ok c24 from rfl) add24 ?_
  refine .step (by change 24>0; omega) (JFr_IndexArithmetic.sub 24#usize 23#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32) from rfl) mul23 (show Array.index_usize p 23#usize=ok c23 from rfl) add23 ?_
  refine .step (by change 23>0; omega) (JFr_IndexArithmetic.sub 23#usize 22#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32) from rfl) mul22 (show Array.index_usize p 22#usize=ok c22 from rfl) add22 ?_
  refine .step (by change 22>0; omega) (JFr_IndexArithmetic.sub 22#usize 21#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32) from rfl) mul21 (show Array.index_usize p 21#usize=ok c21 from rfl) add21 ?_
  refine .step (by change 21>0; omega) (JFr_IndexArithmetic.sub 21#usize 20#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32) from rfl) mul20 (show Array.index_usize p 20#usize=ok c20 from rfl) add20 ?_
  refine .step (by change 20>0; omega) (JFr_IndexArithmetic.sub 20#usize 19#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32) from rfl) mul19 (show Array.index_usize p 19#usize=ok c19 from rfl) add19 ?_
  refine .step (by change 19>0; omega) (JFr_IndexArithmetic.sub 19#usize 18#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32) from rfl) mul18 (show Array.index_usize p 18#usize=ok c18 from rfl) add18 ?_
  refine .step (by change 18>0; omega) (JFr_IndexArithmetic.sub 18#usize 17#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32) from rfl) mul17 (show Array.index_usize p 17#usize=ok c17 from rfl) add17 ?_
  refine .step (by change 17>0; omega) (JFr_IndexArithmetic.sub 17#usize 16#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32) from rfl) mul16 (show Array.index_usize p 16#usize=ok c16 from rfl) add16 ?_
  refine .step (by change 16>0; omega) (JFr_IndexArithmetic.sub 16#usize 15#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32) from rfl) mul15 (show Array.index_usize p 15#usize=ok c15 from rfl) add15 ?_
  refine .step (by change 15>0; omega) (JFr_IndexArithmetic.sub 15#usize 14#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32) from rfl) mul14 (show Array.index_usize p 14#usize=ok c14 from rfl) add14 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner03_0
