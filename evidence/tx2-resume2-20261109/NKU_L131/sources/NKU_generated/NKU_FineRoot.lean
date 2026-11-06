import NKU_FineDigestJoin
set_option autoImplicit false
noncomputable section
namespace NKU_FineRoot
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
theorem suffix {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H) (s : NKU.State) :
 NKU_Fold.suffix d hash s=NKU_ResumeRoot.suffix d hash s := by
 simp only [NKU_Fold.suffix,NKU_ResumeRoot.suffix,NKU_FineDigestJoin.installed]
theorem installed {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H) (s : NKU.State) :
 NKU_Fold.G d hash s=NKU_ResumeRoot.G d hash s := by
 simp only [NKU_Fold.G,NKU_ResumeRoot.G,suffix]
theorem source {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H) (s : NKU.State) :
 NKU_Fold.G d hash s=NJU_ResumeObserved.run s.frame.reservation d s.frame.checkpoint s.frame.proof s.frame.publicBytes .S2 hash :=
 (installed d hash s).trans (NKU_ResumeRoot.source d hash s)
theorem cohort {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H) (s : NKU.State) :
 NIL_StatePort.reply (NKU_Fold.G d hash s).result=
 AspisR1Stage2.verifier.resumeWithOps (CheckpointBytes4Ops.ops (NJC_FilledClause.reserved s.frame.reservation))
 d s.frame.checkpoint s.frame.proof s.frame.publicBytes .S2 hash := by
 rw [installed]
 exact NKU_ResumeRoot.cohort d hash s
#print NKU_Fold.G
#print source
#print cohort
#print axioms suffix
#print axioms installed
#print axioms source
#print axioms cohort
end NKU_FineRoot
