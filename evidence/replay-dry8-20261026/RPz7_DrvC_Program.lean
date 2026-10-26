import RPz7_DrvC_Carriers
import RPz7_GExp_IdealValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_Program
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def mapResult {A B : Type} (f : A → B) : Result A → Result B
  | .ok a => .ok (f a) | .fail e => .fail e | .div => .div

def mapProgram {A B : Type} (f : A → B) (p : Program Bytes State A) : Program Bytes State B :=
  bind p (fun a => .done (f a))

def mapCode {A B : Type} (f : A → B) : SdkC_Source.Code A → SdkC_Source.Code B
  | .done a => .done (f a)
  | .step r k => .step r (fun a => mapCode f (k a))
  | .read parts k => .read parts (fun a => mapCode f (k a))

theorem eval_map {A B : Type} (f : A → B) (p : Program Bytes State A) (H : Bytes → State) :
    eval H (mapProgram f p) = ((eval H p).1,f (eval H p).2) := by
  simp only [mapProgram,eval_bind,eval,List.append_nil]

theorem program_map {A B : Type} (f : A → B) (p : SdkC_Source.Code A) :
    SdkC_Oracle.program (mapCode f p) = mapProgram (mapResult f) (SdkC_Oracle.program p) := by
  induction p with
  | done a => rfl
  | step r k ih => cases r with
    | ok a => exact ih a
    | fail e => rfl
    | div => rfl
  | read parts k ih =>
    simp only [mapCode,SdkC_Oracle.program,mapProgram,AspisV8R19.OracleProgramOps.bind]
    congr 1
    funext answer
    exact ih _

theorem mapResult_id {A : Type} (r : Result A) : mapResult id r = r := by cases r <;> rfl

theorem mapResult_comp {A B C : Type} (f : A → B) (g : B → C) (r : Result A) :
    mapResult g (mapResult f r) = mapResult (g ∘ f) r := by cases r <;> rfl

theorem mapCode_source {A B : Type} (f : A → B) (p : SdkC_Source.Code A)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (before : SdkC_Source.Log) :
    SdkC_Source.run hashv (mapCode f p) before =
      (mapResult f (SdkC_Source.run hashv p before).1,(SdkC_Source.run hashv p before).2) := by
  induction p generalizing before with
  | done a => rfl
  | step r k ih => cases r <;> first | rfl | exact ih _ _
  | read parts k ih =>
    cases h : hashv parts <;> simp only [mapCode,SdkC_Source.run,h]
    all_goals first | rfl | exact ih _ _

#print axioms eval_map
#print axioms program_map
#print axioms mapResult_id
#print axioms mapResult_comp
#print axioms mapCode_source
end AspisR1.DrvC_Program
end
