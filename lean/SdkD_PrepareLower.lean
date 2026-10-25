import S1PreparedHashCodeV1
import S1PreparedOracleCodeV1
import SdkC_Oracle
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_PrepareLower
open Aeneas Aeneas.Std Result
namespace Source
abbrev Code := AspisR1PublicPreparation.PreparedHashCode.Code
end Source

/-- Lower explicit typed preparation digest calls into the same SDK syscall
syntax. Association is a local structural law, not an assumed whole result. -/
def lower {A : Type} : Source.Code A → SdkC_Source.Code A
  | .done a => .done a
  | .step r k => .step r (fun a => lower (k a))
  | .digest _ _ parts k => .read parts (fun a => lower (k a))

def Associated (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) {A : Type} : Source.Code A → Prop
  | .done _ => True
  | .step r k => match r with
    | .ok a => Associated hashv (k a)
    | .fail _ => True
    | .div => True
  | .digest D hash parts k => D.digest hash parts = hashv parts ∧ ∀ a, Associated hashv (k a)

theorem erasure (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) {A : Type}
    (code : Source.Code A) (associated : Associated hashv code) :
    CheckpointBytes5Effect.erase (SdkC_Source.dictionary hashv) () (lower code) =
      AspisR1PublicPreparation.PreparedHashCode.erase code := by
  induction code with
  | done a => rfl
  | step r k ih => cases r with
    | ok a => exact ih a associated
    | fail e => rfl
    | div => rfl
  | digest D hash parts k ih =>
    simp only [lower,CheckpointBytes5Effect.erase,
      AspisR1PublicPreparation.PreparedHashCode.erase,SdkC_Source.dictionary,associated.1]
    cases call : hashv parts <;> simp only [bind_tc_ok,bind_tc_fail,bind_tc_div]
    exact ih _ (associated.2 _)

theorem program {A : Type} (code : Source.Code A) :
    SdkC_Oracle.program (lower code) =
      AspisR1PublicPreparation.PreparedHashCode.oracleProgram code := by
  induction code with
  | done a => rfl
  | step r k ih => cases r <;> first | rfl | exact ih _
  | digest D hash parts k ih =>
    simp only [lower,SdkC_Oracle.program,AspisR1PublicPreparation.PreparedHashCode.oracleProgram]
    congr 1
    funext reply
    exact ih _

#print axioms erasure
#print axioms program
end AspisR1.SdkD_PrepareLower
end
