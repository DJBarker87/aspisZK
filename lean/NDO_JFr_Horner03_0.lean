import NDO_JFr_Data03
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner03_0
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data03
def initial : Q := (q 0#u32 0#u32 0#u32 0#u32)
theorem mul27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 0#u32 0#u32 0#u32 0#u32) (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32)=ok (q 0#u32 0#u32 0#u32 0#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) (by change (1142413086 < 2147483647 ∧ 2006134641 < 2147483647) ∧ (1686703278 < 2147483647 ∧ 2011383024 < 2147483647); omega) (by rfl)
#print axioms mul27
theorem add27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 0#u32 0#u32 0#u32 0#u32) c27=ok (q 1951308848#u32 393500233#u32 2091787517#u32 900347662#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) canonical27 (by rfl)
#print axioms add27
theorem mul26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1951308848#u32 393500233#u32 2091787517#u32 900347662#u32) (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32)=ok (q 310582760#u32 1350644019#u32 1731788312#u32 581993232#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1951308848 < 2147483647 ∧ 393500233 < 2147483647) ∧ (2091787517 < 2147483647 ∧ 900347662 < 2147483647); omega) (by change (1142413086 < 2147483647 ∧ 2006134641 < 2147483647) ∧ (1686703278 < 2147483647 ∧ 2011383024 < 2147483647); omega) (by rfl)
#print axioms mul26
theorem add26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 310582760#u32 1350644019#u32 1731788312#u32 581993232#u32) c26=ok (q 1310089016#u32 2073075843#u32 2047165019#u32 538877345#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (310582760 < 2147483647 ∧ 1350644019 < 2147483647) ∧ (1731788312 < 2147483647 ∧ 581993232 < 2147483647); omega) canonical26 (by rfl)
#print axioms add26
theorem mul25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1310089016#u32 2073075843#u32 2047165019#u32 538877345#u32) (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32)=ok (q 917532299#u32 449019813#u32 408976719#u32 1112555379#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1310089016 < 2147483647 ∧ 2073075843 < 2147483647) ∧ (2047165019 < 2147483647 ∧ 538877345 < 2147483647); omega) (by change (1142413086 < 2147483647 ∧ 2006134641 < 2147483647) ∧ (1686703278 < 2147483647 ∧ 2011383024 < 2147483647); omega) (by rfl)
#print axioms mul25
theorem add25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 917532299#u32 449019813#u32 408976719#u32 1112555379#u32) c25=ok (q 331917884#u32 1128981882#u32 515177402#u32 423433012#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (917532299 < 2147483647 ∧ 449019813 < 2147483647) ∧ (408976719 < 2147483647 ∧ 1112555379 < 2147483647); omega) canonical25 (by rfl)
#print axioms add25
theorem mul24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 331917884#u32 1128981882#u32 515177402#u32 423433012#u32) (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32)=ok (q 1689903143#u32 167223515#u32 308449812#u32 1809538588#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (331917884 < 2147483647 ∧ 1128981882 < 2147483647) ∧ (515177402 < 2147483647 ∧ 423433012 < 2147483647); omega) (by change (1142413086 < 2147483647 ∧ 2006134641 < 2147483647) ∧ (1686703278 < 2147483647 ∧ 2011383024 < 2147483647); omega) (by rfl)
#print axioms mul24
theorem add24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1689903143#u32 167223515#u32 308449812#u32 1809538588#u32) c24=ok (q 356834590#u32 849462134#u32 117295808#u32 704595237#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1689903143 < 2147483647 ∧ 167223515 < 2147483647) ∧ (308449812 < 2147483647 ∧ 1809538588 < 2147483647); omega) canonical24 (by rfl)
#print axioms add24
theorem mul23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 356834590#u32 849462134#u32 117295808#u32 704595237#u32) (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32)=ok (q 1814599354#u32 1700994898#u32 1047567022#u32 2089180711#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (356834590 < 2147483647 ∧ 849462134 < 2147483647) ∧ (117295808 < 2147483647 ∧ 704595237 < 2147483647); omega) (by change (1142413086 < 2147483647 ∧ 2006134641 < 2147483647) ∧ (1686703278 < 2147483647 ∧ 2011383024 < 2147483647); omega) (by rfl)
#print axioms mul23
theorem add23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1814599354#u32 1700994898#u32 1047567022#u32 2089180711#u32) c23=ok (q 1149336428#u32 2065163395#u32 450597237#u32 219110303#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1814599354 < 2147483647 ∧ 1700994898 < 2147483647) ∧ (1047567022 < 2147483647 ∧ 2089180711 < 2147483647); omega) canonical23 (by rfl)
#print axioms add23
theorem mul22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1149336428#u32 2065163395#u32 450597237#u32 219110303#u32) (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32)=ok (q 2020223684#u32 210230541#u32 1987031042#u32 1001907163#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1149336428 < 2147483647 ∧ 2065163395 < 2147483647) ∧ (450597237 < 2147483647 ∧ 219110303 < 2147483647); omega) (by change (1142413086 < 2147483647 ∧ 2006134641 < 2147483647) ∧ (1686703278 < 2147483647 ∧ 2011383024 < 2147483647); omega) (by rfl)
#print axioms mul22
theorem add22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2020223684#u32 210230541#u32 1987031042#u32 1001907163#u32) c22=ok (q 1830293846#u32 1060715176#u32 205661720#u32 234026764#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2020223684 < 2147483647 ∧ 210230541 < 2147483647) ∧ (1987031042 < 2147483647 ∧ 1001907163 < 2147483647); omega) canonical22 (by rfl)
#print axioms add22
theorem mul21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1830293846#u32 1060715176#u32 205661720#u32 234026764#u32) (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32)=ok (q 885974584#u32 132510246#u32 1012676698#u32 45209084#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1830293846 < 2147483647 ∧ 1060715176 < 2147483647) ∧ (205661720 < 2147483647 ∧ 234026764 < 2147483647); omega) (by change (1142413086 < 2147483647 ∧ 2006134641 < 2147483647) ∧ (1686703278 < 2147483647 ∧ 2011383024 < 2147483647); omega) (by rfl)
#print axioms mul21
theorem add21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 885974584#u32 132510246#u32 1012676698#u32 45209084#u32) c21=ok (q 749628441#u32 1793120881#u32 1832993217#u32 148917236#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (885974584 < 2147483647 ∧ 132510246 < 2147483647) ∧ (1012676698 < 2147483647 ∧ 45209084 < 2147483647); omega) canonical21 (by rfl)
#print axioms add21
theorem mul20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 749628441#u32 1793120881#u32 1832993217#u32 148917236#u32) (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32)=ok (q 877393872#u32 1233179280#u32 435283175#u32 238599160#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (749628441 < 2147483647 ∧ 1793120881 < 2147483647) ∧ (1832993217 < 2147483647 ∧ 148917236 < 2147483647); omega) (by change (1142413086 < 2147483647 ∧ 2006134641 < 2147483647) ∧ (1686703278 < 2147483647 ∧ 2011383024 < 2147483647); omega) (by rfl)
#print axioms mul20
theorem add20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 877393872#u32 1233179280#u32 435283175#u32 238599160#u32) c20=ok (q 334757551#u32 541124408#u32 545471756#u32 17498568#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (877393872 < 2147483647 ∧ 1233179280 < 2147483647) ∧ (435283175 < 2147483647 ∧ 238599160 < 2147483647); omega) canonical20 (by rfl)
#print axioms add20
theorem mul19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 334757551#u32 541124408#u32 545471756#u32 17498568#u32) (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32)=ok (q 528414243#u32 2046779683#u32 1526603060#u32 1278823832#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (334757551 < 2147483647 ∧ 541124408 < 2147483647) ∧ (545471756 < 2147483647 ∧ 17498568 < 2147483647); omega) (by change (1142413086 < 2147483647 ∧ 2006134641 < 2147483647) ∧ (1686703278 < 2147483647 ∧ 2011383024 < 2147483647); omega) (by rfl)
#print axioms mul19
theorem add19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 528414243#u32 2046779683#u32 1526603060#u32 1278823832#u32) c19=ok (q 336021174#u32 618647072#u32 1654326058#u32 825633813#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (528414243 < 2147483647 ∧ 2046779683 < 2147483647) ∧ (1526603060 < 2147483647 ∧ 1278823832 < 2147483647); omega) canonical19 (by rfl)
#print axioms add19
theorem mul18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 336021174#u32 618647072#u32 1654326058#u32 825633813#u32) (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32)=ok (q 2092068970#u32 1921772172#u32 485263562#u32 642334312#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (336021174 < 2147483647 ∧ 618647072 < 2147483647) ∧ (1654326058 < 2147483647 ∧ 825633813 < 2147483647); omega) (by change (1142413086 < 2147483647 ∧ 2006134641 < 2147483647) ∧ (1686703278 < 2147483647 ∧ 2011383024 < 2147483647); omega) (by rfl)
#print axioms mul18
theorem add18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2092068970#u32 1921772172#u32 485263562#u32 642334312#u32) c18=ok (q 1131695347#u32 888668340#u32 1453022145#u32 1675398976#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2092068970 < 2147483647 ∧ 1921772172 < 2147483647) ∧ (485263562 < 2147483647 ∧ 642334312 < 2147483647); omega) canonical18 (by rfl)
#print axioms add18
theorem mul17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1131695347#u32 888668340#u32 1453022145#u32 1675398976#u32) (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32)=ok (q 388185474#u32 524889752#u32 1958761927#u32 131414424#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1131695347 < 2147483647 ∧ 888668340 < 2147483647) ∧ (1453022145 < 2147483647 ∧ 1675398976 < 2147483647); omega) (by change (1142413086 < 2147483647 ∧ 2006134641 < 2147483647) ∧ (1686703278 < 2147483647 ∧ 2011383024 < 2147483647); omega) (by rfl)
#print axioms mul17
theorem add17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 388185474#u32 524889752#u32 1958761927#u32 131414424#u32) c17=ok (q 223461448#u32 1408727177#u32 346913469#u32 380677406#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (388185474 < 2147483647 ∧ 524889752 < 2147483647) ∧ (1958761927 < 2147483647 ∧ 131414424 < 2147483647); omega) canonical17 (by rfl)
#print axioms add17
theorem mul16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 223461448#u32 1408727177#u32 346913469#u32 380677406#u32) (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32)=ok (q 554209446#u32 645999525#u32 564101416#u32 704127407#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (223461448 < 2147483647 ∧ 1408727177 < 2147483647) ∧ (346913469 < 2147483647 ∧ 380677406 < 2147483647); omega) (by change (1142413086 < 2147483647 ∧ 2006134641 < 2147483647) ∧ (1686703278 < 2147483647 ∧ 2011383024 < 2147483647); omega) (by rfl)
#print axioms mul16
theorem add16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 554209446#u32 645999525#u32 564101416#u32 704127407#u32) c16=ok (q 1704766976#u32 1396028993#u32 785795383#u32 2090660071#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (554209446 < 2147483647 ∧ 645999525 < 2147483647) ∧ (564101416 < 2147483647 ∧ 704127407 < 2147483647); omega) canonical16 (by rfl)
#print axioms add16
theorem mul15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1704766976#u32 1396028993#u32 785795383#u32 2090660071#u32) (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32)=ok (q 1948607616#u32 1996507068#u32 822414709#u32 1117224481#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1704766976 < 2147483647 ∧ 1396028993 < 2147483647) ∧ (785795383 < 2147483647 ∧ 2090660071 < 2147483647); omega) (by change (1142413086 < 2147483647 ∧ 2006134641 < 2147483647) ∧ (1686703278 < 2147483647 ∧ 2011383024 < 2147483647); omega) (by rfl)
#print axioms mul15
theorem add15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1948607616#u32 1996507068#u32 822414709#u32 1117224481#u32) c15=ok (q 1806703235#u32 643495726#u32 1721318949#u32 1490292735#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1948607616 < 2147483647 ∧ 1996507068 < 2147483647) ∧ (822414709 < 2147483647 ∧ 1117224481 < 2147483647); omega) canonical15 (by rfl)
#print axioms add15
theorem mul14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1806703235#u32 643495726#u32 1721318949#u32 1490292735#u32) (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32)=ok (q 388502078#u32 967899988#u32 2048139371#u32 1189726004#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1806703235 < 2147483647 ∧ 643495726 < 2147483647) ∧ (1721318949 < 2147483647 ∧ 1490292735 < 2147483647); omega) (by change (1142413086 < 2147483647 ∧ 2006134641 < 2147483647) ∧ (1686703278 < 2147483647 ∧ 2011383024 < 2147483647); omega) (by rfl)
#print axioms mul14
theorem add14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 388502078#u32 967899988#u32 2048139371#u32 1189726004#u32) c14=ok (q 963747040#u32 1926430192#u32 447166026#u32 2096645527#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (388502078 < 2147483647 ∧ 967899988 < 2147483647) ∧ (2048139371 < 2147483647 ∧ 1189726004 < 2147483647); omega) canonical14 (by rfl)
#print axioms add14
def final : Q := (q 963747040#u32 1926430192#u32 447166026#u32 2096645527#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 3#usize 28#usize initial 14#usize final := by
  refine .step (by change 28>0; omega) (JFr_IndexArithmetic.sub 28#usize 27#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32) from rfl) mul27 (show Array.index_usize p 27#usize=ok c27 from rfl) add27 ?_
  refine .step (by change 27>0; omega) (JFr_IndexArithmetic.sub 27#usize 26#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32) from rfl) mul26 (show Array.index_usize p 26#usize=ok c26 from rfl) add26 ?_
  refine .step (by change 26>0; omega) (JFr_IndexArithmetic.sub 26#usize 25#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32) from rfl) mul25 (show Array.index_usize p 25#usize=ok c25 from rfl) add25 ?_
  refine .step (by change 25>0; omega) (JFr_IndexArithmetic.sub 25#usize 24#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32) from rfl) mul24 (show Array.index_usize p 24#usize=ok c24 from rfl) add24 ?_
  refine .step (by change 24>0; omega) (JFr_IndexArithmetic.sub 24#usize 23#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32) from rfl) mul23 (show Array.index_usize p 23#usize=ok c23 from rfl) add23 ?_
  refine .step (by change 23>0; omega) (JFr_IndexArithmetic.sub 23#usize 22#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32) from rfl) mul22 (show Array.index_usize p 22#usize=ok c22 from rfl) add22 ?_
  refine .step (by change 22>0; omega) (JFr_IndexArithmetic.sub 22#usize 21#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32) from rfl) mul21 (show Array.index_usize p 21#usize=ok c21 from rfl) add21 ?_
  refine .step (by change 21>0; omega) (JFr_IndexArithmetic.sub 21#usize 20#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32) from rfl) mul20 (show Array.index_usize p 20#usize=ok c20 from rfl) add20 ?_
  refine .step (by change 20>0; omega) (JFr_IndexArithmetic.sub 20#usize 19#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32) from rfl) mul19 (show Array.index_usize p 19#usize=ok c19 from rfl) add19 ?_
  refine .step (by change 19>0; omega) (JFr_IndexArithmetic.sub 19#usize 18#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32) from rfl) mul18 (show Array.index_usize p 18#usize=ok c18 from rfl) add18 ?_
  refine .step (by change 18>0; omega) (JFr_IndexArithmetic.sub 18#usize 17#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32) from rfl) mul17 (show Array.index_usize p 17#usize=ok c17 from rfl) add17 ?_
  refine .step (by change 17>0; omega) (JFr_IndexArithmetic.sub 17#usize 16#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32) from rfl) mul16 (show Array.index_usize p 16#usize=ok c16 from rfl) add16 ?_
  refine .step (by change 16>0; omega) (JFr_IndexArithmetic.sub 16#usize 15#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32) from rfl) mul15 (show Array.index_usize p 15#usize=ok c15 from rfl) add15 ?_
  refine .step (by change 15>0; omega) (JFr_IndexArithmetic.sub 15#usize 14#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1142413086#u32 2006134641#u32 1686703278#u32 2011383024#u32) from rfl) mul14 (show Array.index_usize p 14#usize=ok c14 from rfl) add14 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner03_0
