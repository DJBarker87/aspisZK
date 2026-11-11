import NDO_JFr_Data03
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner03_1
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data03
def initial : Q := (q 2094914637#u32 1725791557#u32 1511076010#u32 2070155558#u32)
theorem mul13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2094914637#u32 1725791557#u32 1511076010#u32 2070155558#u32) (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32)=ok (q 1666737261#u32 1909942790#u32 1018391887#u32 2131132118#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2094914637 < 2147483647 ∧ 1725791557 < 2147483647) ∧ (1511076010 < 2147483647 ∧ 2070155558 < 2147483647); omega) (by change (1777472067 < 2147483647 ∧ 823612886 < 2147483647) ∧ (769288371 < 2147483647 ∧ 68548007 < 2147483647); omega) (by rfl)
#print axioms mul13
theorem add13 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1666737261#u32 1909942790#u32 1018391887#u32 2131132118#u32) c13=ok (q 579335381#u32 1361404778#u32 303490421#u32 1994162256#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1666737261 < 2147483647 ∧ 1909942790 < 2147483647) ∧ (1018391887 < 2147483647 ∧ 2131132118 < 2147483647); omega) canonical13 (by rfl)
#print axioms add13
theorem mul12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 579335381#u32 1361404778#u32 303490421#u32 1994162256#u32) (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32)=ok (q 180953225#u32 389987141#u32 108358675#u32 1089766201#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (579335381 < 2147483647 ∧ 1361404778 < 2147483647) ∧ (303490421 < 2147483647 ∧ 1994162256 < 2147483647); omega) (by change (1777472067 < 2147483647 ∧ 823612886 < 2147483647) ∧ (769288371 < 2147483647 ∧ 68548007 < 2147483647); omega) (by rfl)
#print axioms mul12
theorem add12 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 180953225#u32 389987141#u32 108358675#u32 1089766201#u32) c12=ok (q 1557349103#u32 253028378#u32 842104946#u32 558397213#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (180953225 < 2147483647 ∧ 389987141 < 2147483647) ∧ (108358675 < 2147483647 ∧ 1089766201 < 2147483647); omega) canonical12 (by rfl)
#print axioms add12
theorem mul11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1557349103#u32 253028378#u32 842104946#u32 558397213#u32) (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32)=ok (q 1820908720#u32 177724565#u32 1494953359#u32 2109196442#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1557349103 < 2147483647 ∧ 253028378 < 2147483647) ∧ (842104946 < 2147483647 ∧ 558397213 < 2147483647); omega) (by change (1777472067 < 2147483647 ∧ 823612886 < 2147483647) ∧ (769288371 < 2147483647 ∧ 68548007 < 2147483647); omega) (by rfl)
#print axioms mul11
theorem add11 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1820908720#u32 177724565#u32 1494953359#u32 2109196442#u32) c11=ok (q 1047431567#u32 732081975#u32 2007164266#u32 2140060585#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1820908720 < 2147483647 ∧ 177724565 < 2147483647) ∧ (1494953359 < 2147483647 ∧ 2109196442 < 2147483647); omega) canonical11 (by rfl)
#print axioms add11
theorem mul10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1047431567#u32 732081975#u32 2007164266#u32 2140060585#u32) (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32)=ok (q 566832092#u32 543889157#u32 433760145#u32 1283766403#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1047431567 < 2147483647 ∧ 732081975 < 2147483647) ∧ (2007164266 < 2147483647 ∧ 2140060585 < 2147483647); omega) (by change (1777472067 < 2147483647 ∧ 823612886 < 2147483647) ∧ (769288371 < 2147483647 ∧ 68548007 < 2147483647); omega) (by rfl)
#print axioms mul10
theorem add10 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 566832092#u32 543889157#u32 433760145#u32 1283766403#u32) c10=ok (q 1173093458#u32 199376413#u32 677043385#u32 1541594802#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (566832092 < 2147483647 ∧ 543889157 < 2147483647) ∧ (433760145 < 2147483647 ∧ 1283766403 < 2147483647); omega) canonical10 (by rfl)
#print axioms add10
theorem mul09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1173093458#u32 199376413#u32 677043385#u32 1541594802#u32) (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32)=ok (q 1702661079#u32 2126391027#u32 307979765#u32 863255110#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1173093458 < 2147483647 ∧ 199376413 < 2147483647) ∧ (677043385 < 2147483647 ∧ 1541594802 < 2147483647); omega) (by change (1777472067 < 2147483647 ∧ 823612886 < 2147483647) ∧ (769288371 < 2147483647 ∧ 68548007 < 2147483647); omega) (by rfl)
#print axioms mul09
theorem add09 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1702661079#u32 2126391027#u32 307979765#u32 863255110#u32) c09=ok (q 2143608283#u32 1480512242#u32 1229266129#u32 1635919983#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1702661079 < 2147483647 ∧ 2126391027 < 2147483647) ∧ (307979765 < 2147483647 ∧ 863255110 < 2147483647); omega) canonical09 (by rfl)
#print axioms add09
theorem mul08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2143608283#u32 1480512242#u32 1229266129#u32 1635919983#u32) (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32)=ok (q 1704372033#u32 259951991#u32 473841463#u32 215922781#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2143608283 < 2147483647 ∧ 1480512242 < 2147483647) ∧ (1229266129 < 2147483647 ∧ 1635919983 < 2147483647); omega) (by change (1777472067 < 2147483647 ∧ 823612886 < 2147483647) ∧ (769288371 < 2147483647 ∧ 68548007 < 2147483647); omega) (by rfl)
#print axioms mul08
theorem add08 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1704372033#u32 259951991#u32 473841463#u32 215922781#u32) c08=ok (q 1431143910#u32 137983651#u32 1056737051#u32 1509533823#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1704372033 < 2147483647 ∧ 259951991 < 2147483647) ∧ (473841463 < 2147483647 ∧ 215922781 < 2147483647); omega) canonical08 (by rfl)
#print axioms add08
theorem mul07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1431143910#u32 137983651#u32 1056737051#u32 1509533823#u32) (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32)=ok (q 1007612607#u32 534149798#u32 504090343#u32 1622145315#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1431143910 < 2147483647 ∧ 137983651 < 2147483647) ∧ (1056737051 < 2147483647 ∧ 1509533823 < 2147483647); omega) (by change (1777472067 < 2147483647 ∧ 823612886 < 2147483647) ∧ (769288371 < 2147483647 ∧ 68548007 < 2147483647); omega) (by rfl)
#print axioms mul07
theorem add07 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1007612607#u32 534149798#u32 504090343#u32 1622145315#u32) c07=ok (q 885850425#u32 1481840072#u32 702304786#u32 947981093#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1007612607 < 2147483647 ∧ 534149798 < 2147483647) ∧ (504090343 < 2147483647 ∧ 1622145315 < 2147483647); omega) canonical07 (by rfl)
#print axioms add07
theorem mul06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 885850425#u32 1481840072#u32 702304786#u32 947981093#u32) (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32)=ok (q 71679594#u32 298651194#u32 344795036#u32 1116668013#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (885850425 < 2147483647 ∧ 1481840072 < 2147483647) ∧ (702304786 < 2147483647 ∧ 947981093 < 2147483647); omega) (by change (1777472067 < 2147483647 ∧ 823612886 < 2147483647) ∧ (769288371 < 2147483647 ∧ 68548007 < 2147483647); omega) (by rfl)
#print axioms mul06
theorem add06 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 71679594#u32 298651194#u32 344795036#u32 1116668013#u32) c06=ok (q 1613126340#u32 1204076937#u32 1350414756#u32 1575790342#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (71679594 < 2147483647 ∧ 298651194 < 2147483647) ∧ (344795036 < 2147483647 ∧ 1116668013 < 2147483647); omega) canonical06 (by rfl)
#print axioms add06
theorem mul05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1613126340#u32 1204076937#u32 1350414756#u32 1575790342#u32) (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32)=ok (q 591673372#u32 1136476537#u32 69391820#u32 1801173559#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1613126340 < 2147483647 ∧ 1204076937 < 2147483647) ∧ (1350414756 < 2147483647 ∧ 1575790342 < 2147483647); omega) (by change (1777472067 < 2147483647 ∧ 823612886 < 2147483647) ∧ (769288371 < 2147483647 ∧ 68548007 < 2147483647); omega) (by rfl)
#print axioms mul05
theorem add05 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 591673372#u32 1136476537#u32 69391820#u32 1801173559#u32) c05=ok (q 1604293264#u32 604789115#u32 806212345#u32 1568095039#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (591673372 < 2147483647 ∧ 1136476537 < 2147483647) ∧ (69391820 < 2147483647 ∧ 1801173559 < 2147483647); omega) canonical05 (by rfl)
#print axioms add05
theorem mul04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1604293264#u32 604789115#u32 806212345#u32 1568095039#u32) (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32)=ok (q 486009177#u32 2050234223#u32 1574135484#u32 1771031209#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1604293264 < 2147483647 ∧ 604789115 < 2147483647) ∧ (806212345 < 2147483647 ∧ 1568095039 < 2147483647); omega) (by change (1777472067 < 2147483647 ∧ 823612886 < 2147483647) ∧ (769288371 < 2147483647 ∧ 68548007 < 2147483647); omega) (by rfl)
#print axioms mul04
theorem add04 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 486009177#u32 2050234223#u32 1574135484#u32 1771031209#u32) c04=ok (q 757896648#u32 1514534027#u32 376532005#u32 860075694#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (486009177 < 2147483647 ∧ 2050234223 < 2147483647) ∧ (1574135484 < 2147483647 ∧ 1771031209 < 2147483647); omega) canonical04 (by rfl)
#print axioms add04
theorem mul03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 757896648#u32 1514534027#u32 376532005#u32 860075694#u32) (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32)=ok (q 2101925148#u32 1131880024#u32 349841011#u32 224466380#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (757896648 < 2147483647 ∧ 1514534027 < 2147483647) ∧ (376532005 < 2147483647 ∧ 860075694 < 2147483647); omega) (by change (1777472067 < 2147483647 ∧ 823612886 < 2147483647) ∧ (769288371 < 2147483647 ∧ 68548007 < 2147483647); omega) (by rfl)
#print axioms mul03
theorem add03 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2101925148#u32 1131880024#u32 349841011#u32 224466380#u32) c03=ok (q 1723121554#u32 1642669754#u32 1618266394#u32 541898094#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2101925148 < 2147483647 ∧ 1131880024 < 2147483647) ∧ (349841011 < 2147483647 ∧ 224466380 < 2147483647); omega) canonical03 (by rfl)
#print axioms add03
theorem mul02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1723121554#u32 1642669754#u32 1618266394#u32 541898094#u32) (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32)=ok (q 804997363#u32 570832691#u32 1061548047#u32 654370426#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1723121554 < 2147483647 ∧ 1642669754 < 2147483647) ∧ (1618266394 < 2147483647 ∧ 541898094 < 2147483647); omega) (by change (1777472067 < 2147483647 ∧ 823612886 < 2147483647) ∧ (769288371 < 2147483647 ∧ 68548007 < 2147483647); omega) (by rfl)
#print axioms mul02
theorem add02 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 804997363#u32 570832691#u32 1061548047#u32 654370426#u32) c02=ok (q 2133619847#u32 178695976#u32 1569700737#u32 639951990#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (804997363 < 2147483647 ∧ 570832691 < 2147483647) ∧ (1061548047 < 2147483647 ∧ 654370426 < 2147483647); omega) canonical02 (by rfl)
#print axioms add02
theorem mul01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2133619847#u32 178695976#u32 1569700737#u32 639951990#u32) (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32)=ok (q 886932393#u32 466885282#u32 1748443162#u32 1005916129#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2133619847 < 2147483647 ∧ 178695976 < 2147483647) ∧ (1569700737 < 2147483647 ∧ 639951990 < 2147483647); omega) (by change (1777472067 < 2147483647 ∧ 823612886 < 2147483647) ∧ (769288371 < 2147483647 ∧ 68548007 < 2147483647); omega) (by rfl)
#print axioms mul01
theorem add01 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 886932393#u32 466885282#u32 1748443162#u32 1005916129#u32) c01=ok (q 1864226402#u32 1607633467#u32 820797104#u32 284641815#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (886932393 < 2147483647 ∧ 466885282 < 2147483647) ∧ (1748443162 < 2147483647 ∧ 1005916129 < 2147483647); omega) canonical01 (by rfl)
#print axioms add01
theorem mul00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1864226402#u32 1607633467#u32 820797104#u32 284641815#u32) (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32)=ok (q 1275788750#u32 48826148#u32 1663919245#u32 1819982075#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1864226402 < 2147483647 ∧ 1607633467 < 2147483647) ∧ (820797104 < 2147483647 ∧ 284641815 < 2147483647); omega) (by change (1777472067 < 2147483647 ∧ 823612886 < 2147483647) ∧ (769288371 < 2147483647 ∧ 68548007 < 2147483647); omega) (by rfl)
#print axioms mul00
theorem add00 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1275788750#u32 48826148#u32 1663919245#u32 1819982075#u32) c00=ok (q 284774353#u32 465787694#u32 893767942#u32 240763568#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1275788750 < 2147483647 ∧ 48826148 < 2147483647) ∧ (1663919245 < 2147483647 ∧ 1819982075 < 2147483647); omega) canonical00 (by rfl)
#print axioms add00
def final : Q := (q 284774353#u32 465787694#u32 893767942#u32 240763568#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 3#usize 14#usize initial 0#usize final := by
  refine .step (by change 14>0; omega) (JFr_IndexArithmetic.sub 14#usize 13#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32) from rfl) mul13 (show Array.index_usize p 13#usize=ok c13 from rfl) add13 ?_
  refine .step (by change 13>0; omega) (JFr_IndexArithmetic.sub 13#usize 12#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32) from rfl) mul12 (show Array.index_usize p 12#usize=ok c12 from rfl) add12 ?_
  refine .step (by change 12>0; omega) (JFr_IndexArithmetic.sub 12#usize 11#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32) from rfl) mul11 (show Array.index_usize p 11#usize=ok c11 from rfl) add11 ?_
  refine .step (by change 11>0; omega) (JFr_IndexArithmetic.sub 11#usize 10#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32) from rfl) mul10 (show Array.index_usize p 10#usize=ok c10 from rfl) add10 ?_
  refine .step (by change 10>0; omega) (JFr_IndexArithmetic.sub 10#usize 9#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32) from rfl) mul09 (show Array.index_usize p 9#usize=ok c09 from rfl) add09 ?_
  refine .step (by change 9>0; omega) (JFr_IndexArithmetic.sub 9#usize 8#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32) from rfl) mul08 (show Array.index_usize p 8#usize=ok c08 from rfl) add08 ?_
  refine .step (by change 8>0; omega) (JFr_IndexArithmetic.sub 8#usize 7#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32) from rfl) mul07 (show Array.index_usize p 7#usize=ok c07 from rfl) add07 ?_
  refine .step (by change 7>0; omega) (JFr_IndexArithmetic.sub 7#usize 6#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32) from rfl) mul06 (show Array.index_usize p 6#usize=ok c06 from rfl) add06 ?_
  refine .step (by change 6>0; omega) (JFr_IndexArithmetic.sub 6#usize 5#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32) from rfl) mul05 (show Array.index_usize p 5#usize=ok c05 from rfl) add05 ?_
  refine .step (by change 5>0; omega) (JFr_IndexArithmetic.sub 5#usize 4#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32) from rfl) mul04 (show Array.index_usize p 4#usize=ok c04 from rfl) add04 ?_
  refine .step (by change 4>0; omega) (JFr_IndexArithmetic.sub 4#usize 3#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32) from rfl) mul03 (show Array.index_usize p 3#usize=ok c03 from rfl) add03 ?_
  refine .step (by change 3>0; omega) (JFr_IndexArithmetic.sub 3#usize 2#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32) from rfl) mul02 (show Array.index_usize p 2#usize=ok c02 from rfl) add02 ?_
  refine .step (by change 2>0; omega) (JFr_IndexArithmetic.sub 2#usize 1#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32) from rfl) mul01 (show Array.index_usize p 1#usize=ok c01 from rfl) add01 ?_
  refine .step (by change 1>0; omega) (JFr_IndexArithmetic.sub 1#usize 0#usize rfl) (show Array.index_usize alpha 3#usize=ok (q 1777472067#u32 823612886#u32 769288371#u32 68548007#u32) from rfl) mul00 (show Array.index_usize p 0#usize=ok c00 from rfl) add00 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner03_1
