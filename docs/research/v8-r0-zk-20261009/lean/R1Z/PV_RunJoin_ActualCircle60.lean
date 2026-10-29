import R1Z.PV_RunJoin_ActualRun59
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ActualCircle60
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_NativeControl55 (Phase)
open PV_RunJoin_ActualData59
open ProverCommitValueRange47 (embed)
open AspisR1.ExtractedCurrentQM31Exact (decode)
variable [ExternalTypes] [ExternalFuns]

def coordinates (p : Phase) (i : Fin 2) :=
  (embed (decode (PV_RunJoin_SemanticScalar50.raw (PV_RunJoin_SemanticPoints50.read p.sem.z i).x)),
   embed (decode (PV_RunJoin_SemanticScalar50.raw (PV_RunJoin_SemanticPoints50.read p.sem.z i).y)))

theorem actual (p : Phase) (i : Fin 2)
    (unit : (coordinates p i).1^2+(coordinates p i).2^2=1) :
    ((data p).ch.circle i).val=coordinates p i := by
  change (PV_RunJoin_ActualPoint59.point (coordinates p i).1 (coordinates p i).2).val=coordinates p i
  exact PV_RunJoin_ActualPoint59.first (coordinates p i).1 (coordinates p i).2 unit

theorem stored (p : Phase)
    (unit0 : (coordinates p 0).1^2+(coordinates p 0).2^2=1)
    (unit1 : (coordinates p 1).1^2+(coordinates p 1).2^2=1) :
    embed (decode (data p).x0)=((data p).ch.circle 0).val.1 ∧
    embed (decode (data p).y0)=((data p).ch.circle 0).val.2 ∧
    embed (decode (data p).x1)=((data p).ch.circle 1).val.1 ∧
    embed (decode (data p).y1)=((data p).ch.circle 1).val.2 := by
  have h0 := actual p 0 unit0
  have h1 := actual p 1 unit1
  refine ⟨?_,?_,?_,?_⟩
  · exact (congrArg Prod.fst h0).symm
  · exact (congrArg Prod.snd h0).symm
  · exact (congrArg Prod.fst h1).symm
  · exact (congrArg Prod.snd h1).symm

#print axioms actual
#print axioms stored
end R1Z.PV_RunJoin_ActualCircle60
