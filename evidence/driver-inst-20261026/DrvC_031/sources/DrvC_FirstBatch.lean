import DrvC_MapCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_FirstBatch
open Aeneas Aeneas.Std Result
open DrvC_Installation Tx1Q_Carriers

def errorMap {A Err : Type} (f : AspisR1Stage2.verifier.Error → Err) :
    core.result.Result A AspisR1Stage2.verifier.Error → core.result.Result A Err
  | .Ok a => .Ok a | .Err e => .Err (f e)

theorem sourceMap {Err : Type} (f : AspisR1Stage2.verifier.Error → Err)
    (p : SdkC_Source.Code (core.result.Result Unit AspisR1Stage2.verifier.Error)) :
    SdkC_BatchSource.mapCode f p = DrvC_Program.mapCode (errorMap f) p := by
  rw [DrvC_MapCode.map_as_bind]
  rfl

theorem errors (r : core.result.Result Unit AspisR1Stage2.verifier.Error) :
    DrvC_Dictionary.reply id (errorMap Op5T_Install.currentError r) =
      errorMap Op5T_Install.stageError r := by
  cases r with
  | Ok a => rfl
  | Err e => cases e <;> rfl

theorem batch {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (proof : Slice U8) (p : Tx1Q_Carriers.C.P) (root : Array U8 32#usize) :
    DrvC_CallCode.code c (.op5 (digest c) proof (prepared p) root 0#usize ()) =
      DrvC_Program.mapCode (DrvC_Dictionary.reply id)
        (SdkC_BatchSource.currentCode hashv proof p root) := by
  change SdkC_BatchSource.mapCode Op5T_Install.stageError
      (SdkC_BatchSource.code (VTop_Checkpoint.digest (digest c)) () proof p.queries p.roots root 0#usize) = _
  rw [DrvC_BatchDictionary.code (VTop_Checkpoint.digest (digest c)) (SdkC_Source.dictionary hashv)]
  simp only [SdkC_BatchSource.currentCode,sourceMap,DrvC_MapCode.map_comp]
  congr 1
  funext r
  exact (errors r).symm

#print axioms sourceMap
#print axioms errors
#print axioms batch
end AspisR1.DrvC_FirstBatch
end
