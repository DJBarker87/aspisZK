import NNG_TotalParse094
import NNG_EraseHead094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ParseReject094
open Aeneas Aeneas.Std Result NMT_tx1 NNG_Context094

theorem call (env : RSL.Env) (proof : Slice U8) (bad : proof.val.length≠57607) :
 NNG_ParseCall094.call env proof=.ok (.Err verifier.Error.Parse) := by
 rw [NNG_ParseCall094.source,LIB_ParseShapeTotal.frozen_wrong_length proof bad]
 rfl
#print axioms call

theorem source {H : Type} (env : RSL.Env) (c : Calls) (parent : Parent H)
 (parse : c.c1 parent.proof=NNG_ParseCall094.call env parent.proof)
 (bad : parent.proof.val.length≠57607) :
 NNG_Context094.body c parent=.ok (.Err verifier.Error.Parse) := by
 rw [←NNG_Suffix094.source]
 unfold NNG_Suffix094.f_guard
 dsimp only
 split
 · rfl
 · unfold NNG_Suffix094.f_r
   dsimp only
   rw [parse,call env parent.proof bad]
   rfl
#print axioms source
end AspisR1.NNG_ParseReject094
