import NDO_JGw_DotTerm
import RPt_JFv_TX2_ArrayMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_DotContext
open Aeneas Aeneas.Std Result
structure Data where
  q : Array U8 608#usize
  slot : Fin 4
  scalars : Fin 26 → U32
  reads : ∀ t, JFr_TX2_ScalarRead.read q
    (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac))
    (JFr_TX2_DotTerm.cursor t.val (by have:=t.isLt;omega))=ok (scalars t)
  canonical : ∀ t, (scalars t).val<2147483647
end AspisR1.JHa_DotContext
end
