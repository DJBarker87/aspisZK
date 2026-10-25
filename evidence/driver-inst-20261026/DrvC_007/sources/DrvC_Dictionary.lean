import DrvC_Installation
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_Dictionary
open Aeneas Aeneas.Std Result
open DrvC_Installation DrvC_Carriers Tx1Q_Carriers

def reply {A B : Type} (f : A → B) :
    core.result.Result A AspisR1CurrentCaller.verifier.Error →
      core.result.Result B VTop_Stages.verifier.Error
  | .Ok a => .Ok (f a)
  | .Err e => .Err (AspisS6CurrentVerifierCarrier.fromError e)

def prepareReply (r : core.result.Result C.P AspisR1CurrentCaller.verifier.Error × Array C.E 29#usize) :=
  (reply prepared r.1,arr e r.2)

/-- Port1's single nominal carrier inventory, populated from the installed
current preparation/writer and installed stage continuation. -/
def ops {F C : Type} (c : Configuration F C) : VTop_Stages.Ops :=
  { stage c with
    op1 := DrvC_Program.mapResult e (AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact.ZERO (currentInstalled c))
    op4 := fun proof => DrvC_Program.mapResult (reply id) ((currentInstalled c).op4 proof)
    op7 := fun D pub proof hash obs scratch =>
      DrvC_Program.mapResult prepareReply
        (AspisR1CurrentCaller.verifier.candidate.prepare (currentInstalled c)
          (AspisS6CurrentFirstInstallation.toDigest D)
          (AspisS6CurrentVerifierCarrier.toPublic pub) proof hash
          (AspisS6CurrentFirstInstallation.toObserver obs) (arr unE scratch))
    op8 := fun D p a proof pub hash =>
      (AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact.ZERO (currentInstalled c))6 (AspisS6CurrentFirstInstallation.toDigest D)
        (unPrepared p) (unAccumulator a) proof pub hash
    op12 := fun v => DrvC_Program.mapResult (reply accumulator)
      ((currentInstalled c).op20 (unVariant v)) }

theorem stage_shape {F C : Type} (c : Configuration F C) : (ops c).op3 = (stage c).op3 := rfl

theorem stage_finish {F C : Type} (c : Configuration F C) : (ops c).op19 =
    Port4D_FinishInstall.finish c.finish := rfl

theorem current_writer {F C H : Type} (c : Configuration F C)
    (D : VTop_Stages.aspis_core.digest.Digest32 H) (hash : H)
    (p : Tx1Q_Carriers.C.P) (a : Tx1Q_Carriers.C.A) (proof pub : Slice U8) :
    (ops c).op8 D (prepared p) (accumulator a) proof pub hash =
      (AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact.ZERO (currentInstalled c))6 (AspisS6CurrentFirstInstallation.toDigest D) p a proof pub hash := by
  simp only [ops,current_prepared_roundtrip,current_roundtrip]

#print axioms stage_shape
#print axioms stage_finish
#print axioms current_writer
end AspisR1.DrvC_Dictionary
end
