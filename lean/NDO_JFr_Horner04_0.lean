import NDO_JFr_Data04
import NDO_JFr_HornerTrace
set_option autoImplicit false
namespace AspisR1.JFr_Horner04_0
open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data04
def initial : Q := (q 0#u32 0#u32 0#u32 0#u32)
theorem mul27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 0#u32 0#u32 0#u32 0#u32) (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32)=ok (q 0#u32 0#u32 0#u32 0#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) (by change (1106424694 < 2147483647 ∧ 342809735 < 2147483647) ∧ (1036886578 < 2147483647 ∧ 305075687 < 2147483647); omega) (by rfl)
#print axioms mul27
theorem add27 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 0#u32 0#u32 0#u32 0#u32) c27=ok (q 1024374084#u32 479510156#u32 660870364#u32 698343457#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (0 < 2147483647 ∧ 0 < 2147483647) ∧ (0 < 2147483647 ∧ 0 < 2147483647); omega) canonical27 (by rfl)
#print axioms add27
theorem mul26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1024374084#u32 479510156#u32 660870364#u32 698343457#u32) (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32)=ok (q 1130853151#u32 584744082#u32 1763904735#u32 1583978518#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1024374084 < 2147483647 ∧ 479510156 < 2147483647) ∧ (660870364 < 2147483647 ∧ 698343457 < 2147483647); omega) (by change (1106424694 < 2147483647 ∧ 342809735 < 2147483647) ∧ (1036886578 < 2147483647 ∧ 305075687 < 2147483647); omega) (by rfl)
#print axioms mul26
theorem add26 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1130853151#u32 584744082#u32 1763904735#u32 1583978518#u32) c26=ok (q 908564895#u32 505629228#u32 1306607073#u32 1166672193#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1130853151 < 2147483647 ∧ 584744082 < 2147483647) ∧ (1763904735 < 2147483647 ∧ 1583978518 < 2147483647); omega) canonical26 (by rfl)
#print axioms add26
theorem mul25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 908564895#u32 505629228#u32 1306607073#u32 1166672193#u32) (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32)=ok (q 397784262#u32 616378612#u32 287866203#u32 1772769435#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (908564895 < 2147483647 ∧ 505629228 < 2147483647) ∧ (1306607073 < 2147483647 ∧ 1166672193 < 2147483647); omega) (by change (1106424694 < 2147483647 ∧ 342809735 < 2147483647) ∧ (1036886578 < 2147483647 ∧ 305075687 < 2147483647); omega) (by rfl)
#print axioms mul25
theorem add25 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 397784262#u32 616378612#u32 287866203#u32 1772769435#u32) c25=ok (q 1151863119#u32 1451384783#u32 610317747#u32 50074729#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (397784262 < 2147483647 ∧ 616378612 < 2147483647) ∧ (287866203 < 2147483647 ∧ 1772769435 < 2147483647); omega) canonical25 (by rfl)
#print axioms add25
theorem mul24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1151863119#u32 1451384783#u32 610317747#u32 50074729#u32) (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32)=ok (q 1865139975#u32 327832471#u32 852926551#u32 493246121#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1151863119 < 2147483647 ∧ 1451384783 < 2147483647) ∧ (610317747 < 2147483647 ∧ 50074729 < 2147483647); omega) (by change (1106424694 < 2147483647 ∧ 342809735 < 2147483647) ∧ (1036886578 < 2147483647 ∧ 305075687 < 2147483647); omega) (by rfl)
#print axioms mul24
theorem add24 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1865139975#u32 327832471#u32 852926551#u32 493246121#u32) c24=ok (q 416161485#u32 50510614#u32 639536595#u32 1288556815#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1865139975 < 2147483647 ∧ 327832471 < 2147483647) ∧ (852926551 < 2147483647 ∧ 493246121 < 2147483647); omega) canonical24 (by rfl)
#print axioms add24
theorem mul23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 416161485#u32 50510614#u32 639536595#u32 1288556815#u32) (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32)=ok (q 538978156#u32 437555427#u32 990812237#u32 1983265056#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (416161485 < 2147483647 ∧ 50510614 < 2147483647) ∧ (639536595 < 2147483647 ∧ 1288556815 < 2147483647); omega) (by change (1106424694 < 2147483647 ∧ 342809735 < 2147483647) ∧ (1036886578 < 2147483647 ∧ 305075687 < 2147483647); omega) (by rfl)
#print axioms mul23
theorem add23 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 538978156#u32 437555427#u32 990812237#u32 1983265056#u32) c23=ok (q 590288640#u32 1133978332#u32 228586557#u32 271759109#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (538978156 < 2147483647 ∧ 437555427 < 2147483647) ∧ (990812237 < 2147483647 ∧ 1983265056 < 2147483647); omega) canonical23 (by rfl)
#print axioms add23
theorem mul22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 590288640#u32 1133978332#u32 228586557#u32 271759109#u32) (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32)=ok (q 878193935#u32 744523827#u32 921722219#u32 1137658606#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (590288640 < 2147483647 ∧ 1133978332 < 2147483647) ∧ (228586557 < 2147483647 ∧ 271759109 < 2147483647); omega) (by change (1106424694 < 2147483647 ∧ 342809735 < 2147483647) ∧ (1036886578 < 2147483647 ∧ 305075687 < 2147483647); omega) (by rfl)
#print axioms mul22
theorem add22 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 878193935#u32 744523827#u32 921722219#u32 1137658606#u32) c22=ok (q 685257970#u32 243429826#u32 21037787#u32 1207203991#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (878193935 < 2147483647 ∧ 744523827 < 2147483647) ∧ (921722219 < 2147483647 ∧ 1137658606 < 2147483647); omega) canonical22 (by rfl)
#print axioms add22
theorem mul21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 685257970#u32 243429826#u32 21037787#u32 1207203991#u32) (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32)=ok (q 475727517#u32 2056957777#u32 1094506911#u32 140064380#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (685257970 < 2147483647 ∧ 243429826 < 2147483647) ∧ (21037787 < 2147483647 ∧ 1207203991 < 2147483647); omega) (by change (1106424694 < 2147483647 ∧ 342809735 < 2147483647) ∧ (1036886578 < 2147483647 ∧ 305075687 < 2147483647); omega) (by rfl)
#print axioms mul21
theorem add21 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 475727517#u32 2056957777#u32 1094506911#u32 140064380#u32) c21=ok (q 1954856058#u32 613667315#u32 877333254#u32 744113564#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (475727517 < 2147483647 ∧ 2056957777 < 2147483647) ∧ (1094506911 < 2147483647 ∧ 140064380 < 2147483647); omega) canonical21 (by rfl)
#print axioms add21
theorem mul20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1954856058#u32 613667315#u32 877333254#u32 744113564#u32) (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32)=ok (q 2024838795#u32 543538007#u32 958141946#u32 1824370292#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1954856058 < 2147483647 ∧ 613667315 < 2147483647) ∧ (877333254 < 2147483647 ∧ 744113564 < 2147483647); omega) (by change (1106424694 < 2147483647 ∧ 342809735 < 2147483647) ∧ (1036886578 < 2147483647 ∧ 305075687 < 2147483647); omega) (by rfl)
#print axioms mul20
theorem add20 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 2024838795#u32 543538007#u32 958141946#u32 1824370292#u32) c20=ok (q 2025886055#u32 781974790#u32 155713090#u32 1710725396#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (2024838795 < 2147483647 ∧ 543538007 < 2147483647) ∧ (958141946 < 2147483647 ∧ 1824370292 < 2147483647); omega) canonical20 (by rfl)
#print axioms add20
theorem mul19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2025886055#u32 781974790#u32 155713090#u32 1710725396#u32) (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32)=ok (q 954191888#u32 1915440935#u32 810682963#u32 9390547#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2025886055 < 2147483647 ∧ 781974790 < 2147483647) ∧ (155713090 < 2147483647 ∧ 1710725396 < 2147483647); omega) (by change (1106424694 < 2147483647 ∧ 342809735 < 2147483647) ∧ (1036886578 < 2147483647 ∧ 305075687 < 2147483647); omega) (by rfl)
#print axioms mul19
theorem add19 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 954191888#u32 1915440935#u32 810682963#u32 9390547#u32) c19=ok (q 452150901#u32 2011468862#u32 1855723694#u32 62071254#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (954191888 < 2147483647 ∧ 1915440935 < 2147483647) ∧ (810682963 < 2147483647 ∧ 9390547 < 2147483647); omega) canonical19 (by rfl)
#print axioms add19
theorem mul18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 452150901#u32 2011468862#u32 1855723694#u32 62071254#u32) (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32)=ok (q 189932706#u32 714772838#u32 831587953#u32 1090124081#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (452150901 < 2147483647 ∧ 2011468862 < 2147483647) ∧ (1855723694 < 2147483647 ∧ 62071254 < 2147483647); omega) (by change (1106424694 < 2147483647 ∧ 342809735 < 2147483647) ∧ (1036886578 < 2147483647 ∧ 305075687 < 2147483647); omega) (by rfl)
#print axioms mul18
theorem add18 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 189932706#u32 714772838#u32 831587953#u32 1090124081#u32) c18=ok (q 2125180054#u32 2073748110#u32 327020596#u32 492134642#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (189932706 < 2147483647 ∧ 714772838 < 2147483647) ∧ (831587953 < 2147483647 ∧ 1090124081 < 2147483647); omega) canonical18 (by rfl)
#print axioms add18
theorem mul17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 2125180054#u32 2073748110#u32 327020596#u32 492134642#u32) (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32)=ok (q 1144802884#u32 412337775#u32 457163697#u32 2112622286#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (2125180054 < 2147483647 ∧ 2073748110 < 2147483647) ∧ (327020596 < 2147483647 ∧ 492134642 < 2147483647); omega) (by change (1106424694 < 2147483647 ∧ 342809735 < 2147483647) ∧ (1036886578 < 2147483647 ∧ 305075687 < 2147483647); omega) (by rfl)
#print axioms mul17
theorem add17 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1144802884#u32 412337775#u32 457163697#u32 2112622286#u32) c17=ok (q 1536117160#u32 48304715#u32 835152626#u32 1150846229#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1144802884 < 2147483647 ∧ 412337775 < 2147483647) ∧ (457163697 < 2147483647 ∧ 2112622286 < 2147483647); omega) canonical17 (by rfl)
#print axioms add17
theorem mul16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 1536117160#u32 48304715#u32 835152626#u32 1150846229#u32) (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32)=ok (q 199507464#u32 1697960811#u32 1978099093#u32 1404579064#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (1536117160 < 2147483647 ∧ 48304715 < 2147483647) ∧ (835152626 < 2147483647 ∧ 1150846229 < 2147483647); omega) (by change (1106424694 < 2147483647 ∧ 342809735 < 2147483647) ∧ (1036886578 < 2147483647 ∧ 305075687 < 2147483647); omega) (by rfl)
#print axioms mul16
theorem add16 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 199507464#u32 1697960811#u32 1978099093#u32 1404579064#u32) c16=ok (q 35563364#u32 393855052#u32 271014991#u32 992188756#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (199507464 < 2147483647 ∧ 1697960811 < 2147483647) ∧ (1978099093 < 2147483647 ∧ 1404579064 < 2147483647); omega) canonical16 (by rfl)
#print axioms add16
theorem mul15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 35563364#u32 393855052#u32 271014991#u32 992188756#u32) (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32)=ok (q 327529899#u32 1490769118#u32 1773473371#u32 835784232#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (35563364 < 2147483647 ∧ 393855052 < 2147483647) ∧ (271014991 < 2147483647 ∧ 992188756 < 2147483647); omega) (by change (1106424694 < 2147483647 ∧ 342809735 < 2147483647) ∧ (1036886578 < 2147483647 ∧ 305075687 < 2147483647); omega) (by rfl)
#print axioms mul15
theorem add15 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 327529899#u32 1490769118#u32 1773473371#u32 835784232#u32) c15=ok (q 48067419#u32 1718837046#u32 1395342198#u32 1813555755#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (327529899 < 2147483647 ∧ 1490769118 < 2147483647) ∧ (1773473371 < 2147483647 ∧ 835784232 < 2147483647); omega) canonical15 (by rfl)
#print axioms add15
theorem mul14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul (q 48067419#u32 1718837046#u32 1395342198#u32 1813555755#u32) (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32)=ok (q 1577505727#u32 2135787474#u32 738944580#u32 225943818#u32) :=
  JFr_WordArithmetic.mul _ _ _ (by change (48067419 < 2147483647 ∧ 1718837046 < 2147483647) ∧ (1395342198 < 2147483647 ∧ 1813555755 < 2147483647); omega) (by change (1106424694 < 2147483647 ∧ 342809735 < 2147483647) ∧ (1036886578 < 2147483647 ∧ 305075687 < 2147483647); omega) (by rfl)
#print axioms mul14
theorem add14 : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add (q 1577505727#u32 2135787474#u32 738944580#u32 225943818#u32) c14=ok (q 632766064#u32 450267381#u32 531122620#u32 1261043823#u32) :=
  JFr_WordArithmetic.add _ _ _ (by change (1577505727 < 2147483647 ∧ 2135787474 < 2147483647) ∧ (738944580 < 2147483647 ∧ 225943818 < 2147483647); omega) canonical14 (by rfl)
#print axioms add14
def final : Q := (q 632766064#u32 450267381#u32 531122620#u32 1261043823#u32)
theorem trace : JFr_HornerTrace.Segment p alpha 4#usize 28#usize initial 14#usize final := by
  refine .step (by change 28>0; omega) (JFr_IndexArithmetic.sub 28#usize 27#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32) from rfl) mul27 (show Array.index_usize p 27#usize=ok c27 from rfl) add27 ?_
  refine .step (by change 27>0; omega) (JFr_IndexArithmetic.sub 27#usize 26#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32) from rfl) mul26 (show Array.index_usize p 26#usize=ok c26 from rfl) add26 ?_
  refine .step (by change 26>0; omega) (JFr_IndexArithmetic.sub 26#usize 25#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32) from rfl) mul25 (show Array.index_usize p 25#usize=ok c25 from rfl) add25 ?_
  refine .step (by change 25>0; omega) (JFr_IndexArithmetic.sub 25#usize 24#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32) from rfl) mul24 (show Array.index_usize p 24#usize=ok c24 from rfl) add24 ?_
  refine .step (by change 24>0; omega) (JFr_IndexArithmetic.sub 24#usize 23#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32) from rfl) mul23 (show Array.index_usize p 23#usize=ok c23 from rfl) add23 ?_
  refine .step (by change 23>0; omega) (JFr_IndexArithmetic.sub 23#usize 22#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32) from rfl) mul22 (show Array.index_usize p 22#usize=ok c22 from rfl) add22 ?_
  refine .step (by change 22>0; omega) (JFr_IndexArithmetic.sub 22#usize 21#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32) from rfl) mul21 (show Array.index_usize p 21#usize=ok c21 from rfl) add21 ?_
  refine .step (by change 21>0; omega) (JFr_IndexArithmetic.sub 21#usize 20#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32) from rfl) mul20 (show Array.index_usize p 20#usize=ok c20 from rfl) add20 ?_
  refine .step (by change 20>0; omega) (JFr_IndexArithmetic.sub 20#usize 19#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32) from rfl) mul19 (show Array.index_usize p 19#usize=ok c19 from rfl) add19 ?_
  refine .step (by change 19>0; omega) (JFr_IndexArithmetic.sub 19#usize 18#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32) from rfl) mul18 (show Array.index_usize p 18#usize=ok c18 from rfl) add18 ?_
  refine .step (by change 18>0; omega) (JFr_IndexArithmetic.sub 18#usize 17#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32) from rfl) mul17 (show Array.index_usize p 17#usize=ok c17 from rfl) add17 ?_
  refine .step (by change 17>0; omega) (JFr_IndexArithmetic.sub 17#usize 16#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32) from rfl) mul16 (show Array.index_usize p 16#usize=ok c16 from rfl) add16 ?_
  refine .step (by change 16>0; omega) (JFr_IndexArithmetic.sub 16#usize 15#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32) from rfl) mul15 (show Array.index_usize p 15#usize=ok c15 from rfl) add15 ?_
  refine .step (by change 15>0; omega) (JFr_IndexArithmetic.sub 15#usize 14#usize rfl) (show Array.index_usize alpha 4#usize=ok (q 1106424694#u32 342809735#u32 1036886578#u32 305075687#u32) from rfl) mul14 (show Array.index_usize p 14#usize=ok c14 from rfl) add14 ?_
  exact .refl _ _
#print axioms trace
end AspisR1.JFr_Horner04_0
