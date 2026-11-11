import NDO_JFr_Data07
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner07_0
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data07
def initial : Q := (q 0#u32 0#u32 0#u32 0#u32)
theorem mul27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 0#u32 0#u32 0#u32 0#u32) (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32)=ok (q 0#u32 0#u32 0#u32 0#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) (by change (562817633 < 2147483647 ∧ 1940768295 < 2147483647) ∧ (892660560 < 2147483647 ∧ 287439637 < 2147483647); omega) (by rfl)
#print axioms mul27
theorem add27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 0#u32 0#u32 0#u32 0#u32) c27=ok (q 1486188521#u32 1215583683#u32 144359477#u32 1218290712#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) canonical27 (by rfl)
#print axioms add27
theorem mul26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1486188521#u32 1215583683#u32 144359477#u32 1218290712#u32) (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32)=ok (q 474158286#u32 1423651943#u32 1823620885#u32 759958263#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1486188521 < 2147483647 ∧ 1215583683 < 2147483647) ∧ (144359477 < 2147483647 ∧ 1218290712 < 2147483647); omega) (by change (562817633 < 2147483647 ∧ 1940768295 < 2147483647) ∧ (892660560 < 2147483647 ∧ 287439637 < 2147483647); omega) (by rfl)
#print axioms mul26
theorem add26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 474158286#u32 1423651943#u32 1823620885#u32 759958263#u32) c26=ok (q 1249338024#u32 1889051642#u32 1532324943#u32 427942883#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (474158286 < 2147483647 ∧ 1423651943 < 2147483647) ∧ (1823620885 < 2147483647 ∧ 759958263 < 2147483647); omega) canonical26 (by rfl)
#print axioms add26
theorem mul25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1249338024#u32 1889051642#u32 1532324943#u32 427942883#u32) (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32)=ok (q 2080201352#u32 1155421067#u32 2031028156#u32 136346234#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1249338024 < 2147483647 ∧ 1889051642 < 2147483647) ∧ (1532324943 < 2147483647 ∧ 427942883 < 2147483647); omega) (by change (562817633 < 2147483647 ∧ 1940768295 < 2147483647) ∧ (892660560 < 2147483647 ∧ 287439637 < 2147483647); omega) (by rfl)
#print axioms mul25
theorem add25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2080201352#u32 1155421067#u32 2031028156#u32 136346234#u32) c25=ok (q 1190023300#u32 1977236201#u32 1207070511#u32 1965216620#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2080201352 < 2147483647 ∧ 1155421067 < 2147483647) ∧ (2031028156 < 2147483647 ∧ 136346234 < 2147483647); omega) canonical25 (by rfl)
#print axioms add25
theorem mul24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1190023300#u32 1977236201#u32 1207070511#u32 1965216620#u32) (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32)=ok (q 692220972#u32 1723094136#u32 1046935321#u32 1024951155#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1190023300 < 2147483647 ∧ 1977236201 < 2147483647) ∧ (1207070511 < 2147483647 ∧ 1965216620 < 2147483647); omega) (by change (562817633 < 2147483647 ∧ 1940768295 < 2147483647) ∧ (892660560 < 2147483647 ∧ 287439637 < 2147483647); omega) (by rfl)
#print axioms mul24
theorem add24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 692220972#u32 1723094136#u32 1046935321#u32 1024951155#u32) c24=ok (q 972084323#u32 1212630245#u32 1930950784#u32 1983897205#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (692220972 < 2147483647 ∧ 1723094136 < 2147483647) ∧ (1046935321 < 2147483647 ∧ 1024951155 < 2147483647); omega) canonical24 (by rfl)
#print axioms add24
theorem mul23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 972084323#u32 1212630245#u32 1930950784#u32 1983897205#u32) (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32)=ok (q 1289774524#u32 333535216#u32 1392504682#u32 2063767780#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (972084323 < 2147483647 ∧ 1212630245 < 2147483647) ∧ (1930950784 < 2147483647 ∧ 1983897205 < 2147483647); omega) (by change (562817633 < 2147483647 ∧ 1940768295 < 2147483647) ∧ (892660560 < 2147483647 ∧ 287439637 < 2147483647); omega) (by rfl)
#print axioms mul23
theorem add23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1289774524#u32 333535216#u32 1392504682#u32 2063767780#u32) c23=ok (q 572766134#u32 858432911#u32 378412878#u32 1084811424#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1289774524 < 2147483647 ∧ 333535216 < 2147483647) ∧ (1392504682 < 2147483647 ∧ 2063767780 < 2147483647); omega) canonical23 (by rfl)
#print axioms add23
theorem mul22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 572766134#u32 858432911#u32 378412878#u32 1084811424#u32) (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32)=ok (q 335134276#u32 1834277737#u32 1566512033#u32 371075729#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (572766134 < 2147483647 ∧ 858432911 < 2147483647) ∧ (378412878 < 2147483647 ∧ 1084811424 < 2147483647); omega) (by change (562817633 < 2147483647 ∧ 1940768295 < 2147483647) ∧ (892660560 < 2147483647 ∧ 287439637 < 2147483647); omega) (by rfl)
#print axioms mul22
theorem add22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 335134276#u32 1834277737#u32 1566512033#u32 371075729#u32) c22=ok (q 545548058#u32 913917464#u32 1476528352#u32 47402088#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (335134276 < 2147483647 ∧ 1834277737 < 2147483647) ∧ (1566512033 < 2147483647 ∧ 371075729 < 2147483647); omega) canonical22 (by rfl)
#print axioms add22
theorem mul21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 545548058#u32 913917464#u32 1476528352#u32 47402088#u32) (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32)=ok (q 647398706#u32 1829030106#u32 1379309327#u32 781996930#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (545548058 < 2147483647 ∧ 913917464 < 2147483647) ∧ (1476528352 < 2147483647 ∧ 47402088 < 2147483647); omega) (by change (562817633 < 2147483647 ∧ 1940768295 < 2147483647) ∧ (892660560 < 2147483647 ∧ 287439637 < 2147483647); omega) (by rfl)
#print axioms mul21
theorem add21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 647398706#u32 1829030106#u32 1379309327#u32 781996930#u32) c21=ok (q 389358#u32 1422595943#u32 378713039#u32 369727828#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (647398706 < 2147483647 ∧ 1829030106 < 2147483647) ∧ (1379309327 < 2147483647 ∧ 781996930 < 2147483647); omega) canonical21 (by rfl)
#print axioms add21
theorem mul20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 389358#u32 1422595943#u32 378713039#u32 369727828#u32) (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32)=ok (q 1246411969#u32 84739624#u32 2007617570#u32 191123150#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (389358 < 2147483647 ∧ 1422595943 < 2147483647) ∧ (378713039 < 2147483647 ∧ 369727828 < 2147483647); omega) (by change (562817633 < 2147483647 ∧ 1940768295 < 2147483647) ∧ (892660560 < 2147483647 ∧ 287439637 < 2147483647); omega) (by rfl)
#print axioms mul20
theorem add20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1246411969#u32 84739624#u32 2007617570#u32 191123150#u32) c20=ok (q 2114593771#u32 2136907229#u32 388970778#u32 1377661899#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1246411969 < 2147483647 ∧ 84739624 < 2147483647) ∧ (2007617570 < 2147483647 ∧ 191123150 < 2147483647); omega) canonical20 (by rfl)
#print axioms add20
theorem mul19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2114593771#u32 2136907229#u32 388970778#u32 1377661899#u32) (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32)=ok (q 1629541278#u32 1374293897#u32 1493668409#u32 1428664835#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2114593771 < 2147483647 ∧ 2136907229 < 2147483647) ∧ (388970778 < 2147483647 ∧ 1377661899 < 2147483647); omega) (by change (562817633 < 2147483647 ∧ 1940768295 < 2147483647) ∧ (892660560 < 2147483647 ∧ 287439637 < 2147483647); omega) (by rfl)
#print axioms mul19
theorem add19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1629541278#u32 1374293897#u32 1493668409#u32 1428664835#u32) c19=ok (q 1724604601#u32 1037192147#u32 148271206#u32 1144241251#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1629541278 < 2147483647 ∧ 1374293897 < 2147483647) ∧ (1493668409 < 2147483647 ∧ 1428664835 < 2147483647); omega) canonical19 (by rfl)
#print axioms add19
theorem mul18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1724604601#u32 1037192147#u32 148271206#u32 1144241251#u32) (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32)=ok (q 1300491183#u32 311757361#u32 2032516717#u32 1962087344#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1724604601 < 2147483647 ∧ 1037192147 < 2147483647) ∧ (148271206 < 2147483647 ∧ 1144241251 < 2147483647); omega) (by change (562817633 < 2147483647 ∧ 1940768295 < 2147483647) ∧ (892660560 < 2147483647 ∧ 287439637 < 2147483647); omega) (by rfl)
#print axioms mul18
theorem add18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1300491183#u32 311757361#u32 2032516717#u32 1962087344#u32) c18=ok (q 698461806#u32 1707036563#u32 1800237295#u32 1205086957#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1300491183 < 2147483647 ∧ 311757361 < 2147483647) ∧ (2032516717 < 2147483647 ∧ 1962087344 < 2147483647); omega) canonical18 (by rfl)
#print axioms add18
theorem mul17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 698461806#u32 1707036563#u32 1800237295#u32 1205086957#u32) (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32)=ok (q 35655481#u32 679230826#u32 518068456#u32 1338651044#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (698461806 < 2147483647 ∧ 1707036563 < 2147483647) ∧ (1800237295 < 2147483647 ∧ 1205086957 < 2147483647); omega) (by change (562817633 < 2147483647 ∧ 1940768295 < 2147483647) ∧ (892660560 < 2147483647 ∧ 287439637 < 2147483647); omega) (by rfl)
#print axioms mul17
theorem add17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 35655481#u32 679230826#u32 518068456#u32 1338651044#u32) c17=ok (q 326379282#u32 2146759434#u32 635064578#u32 656771676#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (35655481 < 2147483647 ∧ 679230826 < 2147483647) ∧ (518068456 < 2147483647 ∧ 1338651044 < 2147483647); omega) canonical17 (by rfl)
#print axioms add17
theorem mul16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 326379282#u32 2146759434#u32 635064578#u32 656771676#u32) (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32)=ok (q 726950403#u32 557009711#u32 1670951903#u32 1191333633#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (326379282 < 2147483647 ∧ 2146759434 < 2147483647) ∧ (635064578 < 2147483647 ∧ 656771676 < 2147483647); omega) (by change (562817633 < 2147483647 ∧ 1940768295 < 2147483647) ∧ (892660560 < 2147483647 ∧ 287439637 < 2147483647); omega) (by rfl)
#print axioms mul16
theorem add16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 726950403#u32 557009711#u32 1670951903#u32 1191333633#u32) c16=ok (q 614548882#u32 779475239#u32 2066182050#u32 1908751588#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (726950403 < 2147483647 ∧ 557009711 < 2147483647) ∧ (1670951903 < 2147483647 ∧ 1191333633 < 2147483647); omega) canonical16 (by rfl)
#print axioms add16
theorem mul15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 614548882#u32 779475239#u32 2066182050#u32 1908751588#u32) (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32)=ok (q 367858570#u32 1634471143#u32 1803519763#u32 615663761#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (614548882 < 2147483647 ∧ 779475239 < 2147483647) ∧ (2066182050 < 2147483647 ∧ 1908751588 < 2147483647); omega) (by change (562817633 < 2147483647 ∧ 1940768295 < 2147483647) ∧ (892660560 < 2147483647 ∧ 287439637 < 2147483647); omega) (by rfl)
#print axioms mul15
theorem add15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 367858570#u32 1634471143#u32 1803519763#u32 615663761#u32) c15=ok (q 1061889751#u32 77677410#u32 1456248775#u32 1647259134#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (367858570 < 2147483647 ∧ 1634471143 < 2147483647) ∧ (1803519763 < 2147483647 ∧ 615663761 < 2147483647); omega) canonical15 (by rfl)
#print axioms add15
theorem mul14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1061889751#u32 77677410#u32 1456248775#u32 1647259134#u32) (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32)=ok (q 1305362391#u32 1685969275#u32 662465120#u32 143605905#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1061889751 < 2147483647 ∧ 77677410 < 2147483647) ∧ (1456248775 < 2147483647 ∧ 1647259134 < 2147483647); omega) (by change (562817633 < 2147483647 ∧ 1940768295 < 2147483647) ∧ (892660560 < 2147483647 ∧ 287439637 < 2147483647); omega) (by rfl)
#print axioms mul14
theorem add14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1305362391#u32 1685969275#u32 662465120#u32 143605905#u32) c14=ok (q 828515149#u32 1665862388#u32 987748807#u32 1524896543#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1305362391 < 2147483647 ∧ 1685969275 < 2147483647) ∧ (662465120 < 2147483647 ∧ 143605905 < 2147483647); omega) canonical14 (by rfl)
#print axioms add14
def final : Q := (q 828515149#u32 1665862388#u32 987748807#u32 1524896543#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 7#usize 28#usize initial 14#usize final := by
  refine .step (by change 28>0; omega) (JFr_IndexArithmetic.sub 28#usize 27#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32) from rfl) mul27 (show Array.index_usize p 27#usize=ok c27 from rfl) add27 ?_
  refine .step (by change 27>0; omega) (JFr_IndexArithmetic.sub 27#usize 26#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32) from rfl) mul26 (show Array.index_usize p 26#usize=ok c26 from rfl) add26 ?_
  refine .step (by change 26>0; omega) (JFr_IndexArithmetic.sub 26#usize 25#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32) from rfl) mul25 (show Array.index_usize p 25#usize=ok c25 from rfl) add25 ?_
  refine .step (by change 25>0; omega) (JFr_IndexArithmetic.sub 25#usize 24#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32) from rfl) mul24 (show Array.index_usize p 24#usize=ok c24 from rfl) add24 ?_
  refine .step (by change 24>0; omega) (JFr_IndexArithmetic.sub 24#usize 23#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32) from rfl) mul23 (show Array.index_usize p 23#usize=ok c23 from rfl) add23 ?_
  refine .step (by change 23>0; omega) (JFr_IndexArithmetic.sub 23#usize 22#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32) from rfl) mul22 (show Array.index_usize p 22#usize=ok c22 from rfl) add22 ?_
  refine .step (by change 22>0; omega) (JFr_IndexArithmetic.sub 22#usize 21#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32) from rfl) mul21 (show Array.index_usize p 21#usize=ok c21 from rfl) add21 ?_
  refine .step (by change 21>0; omega) (JFr_IndexArithmetic.sub 21#usize 20#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32) from rfl) mul20 (show Array.index_usize p 20#usize=ok c20 from rfl) add20 ?_
  refine .step (by change 20>0; omega) (JFr_IndexArithmetic.sub 20#usize 19#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32) from rfl) mul19 (show Array.index_usize p 19#usize=ok c19 from rfl) add19 ?_
  refine .step (by change 19>0; omega) (JFr_IndexArithmetic.sub 19#usize 18#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32) from rfl) mul18 (show Array.index_usize p 18#usize=ok c18 from rfl) add18 ?_
  refine .step (by change 18>0; omega) (JFr_IndexArithmetic.sub 18#usize 17#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32) from rfl) mul17 (show Array.index_usize p 17#usize=ok c17 from rfl) add17 ?_
  refine .step (by change 17>0; omega) (JFr_IndexArithmetic.sub 17#usize 16#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32) from rfl) mul16 (show Array.index_usize p 16#usize=ok c16 from rfl) add16 ?_
  refine .step (by change 16>0; omega) (JFr_IndexArithmetic.sub 16#usize 15#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32) from rfl) mul15 (show Array.index_usize p 15#usize=ok c15 from rfl) add15 ?_
  refine .step (by change 15>0; omega) (JFr_IndexArithmetic.sub 15#usize 14#usize rfl) (show Array.index_usize alpha 7#usize=ok (q 562817633#u32 1940768295#u32 892660560#u32 287439637#u32) from rfl) mul14 (show Array.index_usize p 14#usize=ok c14 from rfl) add14 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner07_0
