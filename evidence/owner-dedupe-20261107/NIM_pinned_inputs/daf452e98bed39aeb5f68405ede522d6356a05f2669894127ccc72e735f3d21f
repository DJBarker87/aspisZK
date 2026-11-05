import NGY_FieldOracle
import NGY_Complete
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGY_Unified
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues NGU_LPm_RawPort
open AspisR1CurrentPreparedClaim

/-- One explicit G: first five points have a Dot event; point5 has the pure
field event followed by the Dot event. Every Dot event carries full state. -/
def G (point : Nat) (y1 : Slice U8) (lane : Usize) (before after : Native)
 (coefficient : NE) (semanticScalar : NQ) (fieldReply : NE)
 (pushReply : core.result.Result Unit Unit) :=
 let scalar := if point=5 then fieldReply.c0 else semanticScalar
 (NGY_Result.G lane.val before after coefficient scalar pushReply,
  (if point=5 then [NGY_FieldOracle.Event.field y1 lane fieldReply] else []) ++
   [NGY_FieldOracle.Event.dot ⟨coefficient,scalar,before,after,pushReply⟩])

theorem semantic (point : Nat) (hp : point<5) (y1 : Slice U8) (lane : Usize)
 (before after : Native) (coefficient : NE) (scalar : NQ) (fieldReply : NE)
 (pushReply : core.result.Result Unit Unit) :
 G point y1 lane before after coefficient scalar fieldReply pushReply=
  (NGY_Result.G lane.val before after coefficient scalar pushReply,
   [NGY_FieldOracle.Event.dot ⟨coefficient,scalar,before,after,pushReply⟩]) := by
 have ne : point≠5 := by omega
 simp only [G,if_neg ne,List.nil_append]

theorem decoded (y1 : Slice U8) (lane : Usize) (before after : Native)
 (coefficient : NE) (scalar : NQ) (fieldReply : NE)
 (pushReply : core.result.Result Unit Unit) :
 G 5 y1 lane before after coefficient scalar fieldReply pushReply=
  NGY_FieldOracle.G y1 lane before after coefficient fieldReply pushReply := rfl

/-- Internal field events erase to the existing point-loop operand trace. -/
def operands : List NGY_FieldOracle.Event → List (NE×NQ)
 | [] => []
 | .field _ _ _ :: tail => operands tail
 | .dot entry :: tail => (entry.value,entry.scalar)::operands tail

theorem operand_log (y1 : Slice U8) (lane : Usize) (before after : Native)
 (coefficient fieldReply : NE) (pushReply : core.result.Result Unit Unit) :
 operands (NGY_FieldOracle.G y1 lane before after coefficient fieldReply pushReply).2=
 [(coefficient,fieldReply.c0)] := rfl

#print axioms semantic
#print axioms decoded
#print axioms operand_log
end AspisR1.NGY_Unified
end
