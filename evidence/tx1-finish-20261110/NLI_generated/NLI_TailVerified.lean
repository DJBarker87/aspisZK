import NLI_RunLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
def tailVerified {H : Type} (i : Input H) (root : Array U8 32#usize) (alpha : Alpha)
 (claims : Claims) (extra beforeZ1 : Words) (stateBefore : Array U8 32#usize)
 (z0 z1 : Point) (transcript : r1_wire.SemanticTranscript H) : Code (Out H) :=
 pure (.Ok {roots:=Array.make 2#usize [i.prefix1.c1_root,root],challenges:=i.challenges, alpha:=alpha,claims:=claims,extra:=extra,before_z1:=beforeZ1,state_before_z0:=stateBefore, z:=Array.make 2#usize [z0,z1],transcript:=transcript})
theorem verified {H : Type} (i : Input H) (l : Locals H)
 (root : Array U8 32#usize) (alpha : Alpha) (claims : Claims) (extra beforeZ1 : Words)
 (stateBefore : Array U8 32#usize) (z0 z1 : Point) (transcript : r1_wire.SemanticTranscript H) :
 run (fold 3 {input:=i,next:=.verified,locals:={l with root:=some root,alpha:=some alpha, claims:=some claims,extra:=some extra,beforeZ1:=some beforeZ1,stateBefore:=some stateBefore, z0:=some z0,z1:=some z1,transcript:=some transcript}}) =
 run (tailVerified i root alpha claims extra beforeZ1 stateBefore z0 z1 transcript) := by rfl
#print axioms verified
end AspisR1.NLI_Source
end
