import RPz7_S1PreparedOracleCodeV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedHashCode
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw

def continueOracle {A B : Type} (r : Result A) (k : A → Program Bytes State (Result B)) :
    Program Bytes State (Result B) :=
  match r with
  | .ok a => k a
  | .fail e => .done (.fail e)
  | .div => .done .div

theorem oracleProgram_bind {A B : Type} (p : Code A) (k : A → Code B) :
    oracleProgram (p >>= k)=
      AspisV8R19.OracleProgramOps.bind (oracleProgram p)
        (fun r => continueOracle r (fun a => oracleProgram (k a))) := by
  induction p with
  | done a => rfl
  | step r next ih =>
    cases r with
    | ok a => exact ih a
    | fail e => rfl
    | div => rfl
  | digest D hash parts next ih =>
    change Program.ask (flatten parts) (fun s => oracleProgram (bind (next (encodeState s)) k)) = _
    simp only [oracleProgram,AspisV8R19.OracleProgramOps.bind]
    congr 1
    funext s
    exact ih (encodeState s)

theorem oracleProgram_pure {A : Type} (a : A) :
    oracleProgram (pure a : Code A)=Program.done (ok a) := rfl

theorem oracleProgram_lift {A : Type} (r : Result A) :
    oracleProgram (monadLift r : Code A)=Program.done r := by cases r <;> rfl

theorem oracleProgram_digest {H : Type} (D : aspis_core.Digest32 H) (hash : H)
    (parts : Slice (Slice U8)) :
    oracleProgram (effects.digest D hash parts)=
      Program.ask (flatten parts) (fun s => .done (ok (encodeState s))) := rfl

theorem oracleProgram_bind_congr {A B : Type} (p q : Code A) (f g : A → Code B)
    (hp : oracleProgram p=oracleProgram q)
    (hk : ∀ a, oracleProgram (f a)=oracleProgram (g a)) :
    oracleProgram (p >>= f)=oracleProgram (q >>= g) := by
  rw [oracleProgram_bind,oracleProgram_bind,hp]
  congr 1
  funext r
  cases r <;> simp only [continueOracle,hk]

#print axioms oracleProgram_bind_congr
#print axioms oracleProgram_bind
#print axioms oracleProgram_lift
#print axioms oracleProgram_digest
end AspisR1PublicPreparation.PreparedHashCode
