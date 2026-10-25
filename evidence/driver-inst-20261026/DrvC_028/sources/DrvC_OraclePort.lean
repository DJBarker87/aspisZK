import DrvC_CurrentSlots
import DrvC_Flow
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_OraclePort
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open DrvC_Program
abbrev Port (A : Type) := Program Bytes State (Result A)

def bindR {A B : Type} (p : Port A) (k : A → Port B) : Port B :=
  bind p (fun r => VTop_OracleCode.continueWith r k)

def mapR {A B : Type} (f : A → B) (p : Port A) : Port B := mapProgram (mapResult f) p

theorem bind_assoc {A B C : Type} (p : Program Bytes State A)
    (k : A → Program Bytes State B) (h : B → Program Bytes State C) :
    bind (bind p k) h = bind p (fun a => bind (k a) h) := by
  induction p with
  | done a => rfl
  | ask q next ih =>
    simp only [AspisV8R19.OracleProgramOps.bind]
    congr 1
    funext a
    exact ih a

theorem program_bindM {A B : Type} (p : SdkC_Source.Code A) (k : A → SdkC_Source.Code B) :
    SdkC_Oracle.program (p >>= k) = bindR (SdkC_Oracle.program p)
      (fun a => SdkC_Oracle.program (k a)) := DrvC_CallCode.program_bind p k

theorem program_liftM {A : Type} (r : Result A) :
    SdkC_Oracle.program (CheckpointBytes5Effect.liftResult r) = .done r := DrvC_CallCode.program_lift r

theorem map_bind {A B C : Type} (f : B → C) (p : Port A) (k : A → Port B) :
    mapR f (bindR p k) = bindR p (fun a => mapR f (k a)) := by
  simp only [mapR,mapProgram,bindR,bind_assoc]
  congr 1
  funext r
  cases r <;> rfl

theorem bind_map {A B C : Type} (f : A → B) (p : Port A) (k : B → Port C) :
    bindR (mapR f p) k = bindR p (fun a => k (f a)) := by
  simp only [mapR,mapProgram,bindR,bind_assoc]
  congr 1
  funext r
  cases r <;> rfl

theorem map_pure {A B : Type} (f : A → B) (a : A) :
    mapR f (.done (.ok a)) = .done (.ok (f a)) := rfl

theorem map_lift {A B : Type} (f : A → B) (r : Result A) :
    mapR f (.done r) = .done (mapResult f r) := rfl

theorem bindR_congr {A B : Type} (p : Port A) (k h : A → Port B)
    (eq : ∀ a, k a = h a) : bindR p k = bindR p h := congrArg (bindR p) (funext eq)

#print axioms bind_assoc
#print axioms program_bindM
#print axioms program_liftM
#print axioms map_bind
#print axioms bind_map
#print axioms map_pure
#print axioms map_lift
#print axioms bindR_congr
end AspisR1.DrvC_OraclePort
end
