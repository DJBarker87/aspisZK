import NLC_FinishStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (run)
/-- Exact initialized constructor state. No successful child outcome is assumed:
all supplied fields are arbitrary and are carried unchanged to the output. -/
def constructorLocals {H : Type} (alpha : Alpha) (claims : Claims) (extra before : Words)
 (state root : Array U8 32#usize) (z0 z1 : Point) (transcript : r1_wire.SemanticTranscript H) : Locals H :=
 {alpha:=some alpha,claims:=some claims,extra:=some extra,beforeZ1:=some before,
  stateBefore:=some state,root:=some root,z0:=some z0,z1:=some z1,transcript:=some transcript}
theorem constructor {H : Type} (i : Input H) (alpha : Alpha) (claims : Claims)
 (extra before : Words) (state root : Array U8 32#usize) (z0 z1 : Point)
 (transcript : r1_wire.SemanticTranscript H) :
 run (step {input:=i,locals:=constructorLocals alpha claims extra before state root z0 z1 transcript,next:=.verified}) =
 ([],ok (.inl (.Ok {
   roots := (Array.make 2#usize [i.prefix1.c1_root,root]),challenges:=i.challenges,
   alpha:=alpha,claims:=claims,extra:=extra,before_z1:=before,state_before_z0:=state,
   z:=(Array.make 2#usize [z0,z1]),transcript:=transcript}))) := by rfl
#print axioms constructor
#print constructor
end AspisR1.NLC_Finish
end
