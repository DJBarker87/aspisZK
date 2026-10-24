import S1PreparedHashCodeV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedHashCode
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw

/-- Structural property to be DERIVED for the concrete P3 source dictionary.
This is not accepted as a new native per-call association premise. -/
def OracleValid (sha : Bytes → Array U8 32#usize) {A : Type} : Code A → Prop
  | .done _ => True
  | .step _ k => ∀ a, OracleValid sha (k a)
  | .digest D hash parts k => D.digest hash parts=ok (sha (flatten parts)) ∧
      ∀ a, OracleValid sha (k a)

def oracleProgram {A : Type} : Code A → Program Bytes State (Result A)
  | .done a => .done (ok a)
  | .step r k => match r with
    | .ok a => oracleProgram (k a)
    | .fail e => .done (.fail e)
    | .div => .done .div
  | .digest _ _ parts k => .ask (flatten parts) (fun s => oracleProgram (k (encodeState s)))

/-- Complete ordered successful replies. Under OracleValid every digest reply
is successful; pure steps can still fail/diverge after any prefix. -/
def observe : Log → List (Bytes × State) := List.flatMap fun e =>
  match e with
  | .digest _ _ parts (.ok out) => [(flatten parts,decodeState out)]
  | .digest _ _ _ (.fail _) => []
  | .digest _ _ _ .div => []

theorem valid_pure (sha : Bytes → Array U8 32#usize) {A : Type} (a : A) :
    OracleValid sha (pure a : Code A) := True.intro

theorem valid_lift (sha : Bytes → Array U8 32#usize) {A : Type} (r : Result A) :
    OracleValid sha (monadLift r : Code A) := fun _ => True.intro

theorem valid_digest (sha : Bytes → Array U8 32#usize) {H : Type}
    (D : aspis_core.Digest32 H) (hash : H) (parts : Slice (Slice U8))
    (law : D.digest hash parts=ok (sha (flatten parts))) :
    OracleValid sha (effects.digest D hash parts) := ⟨law,fun _ => True.intro⟩

theorem valid_bind (sha : Bytes → Array U8 32#usize) {A B : Type} (p : Code A)
    (k : A → Code B) (hp : OracleValid sha p) (hk : ∀ a, OracleValid sha (k a)) :
    OracleValid sha (p >>= k) := by
  induction p with
  | done a => exact hk a
  | step r next ih => exact fun a => ih a (hp a)
  | digest D hash parts next ih => exact ⟨hp.1,fun a => ih a (hp.2 a)⟩

/-- Ordered reads AND complete returned Result, retaining rejected suffix
prefixes, repeated queries and the same replies used by continuations. -/
theorem oracleProgram_exact (sha : Bytes → Array U8 32#usize) {A : Type}
    (p : Code A) (valid : OracleValid sha p) :
    eval (fun bytes => decodeState (sha bytes)) (oracleProgram p)=
      (observe (run p).1,(run p).2) := by
  induction p with
  | done a => rfl
  | step r next ih =>
    cases r with
    | ok a => exact ih a (valid a)
    | fail e => rfl
    | div => rfl
  | digest D hash parts next ih =>
    simp only [oracleProgram,eval,array_roundtrip,run,valid.1]
    rw [ih _ (valid.2 _)]
    rfl

theorem oracleProgram_value (sha : Bytes → Array U8 32#usize) {A : Type}
    (p : Code A) (valid : OracleValid sha p) :
    (eval (fun bytes => decodeState (sha bytes)) (oracleProgram p)).2=erase p := by
  rw [oracleProgram_exact sha p valid,run_value]

#print axioms valid_bind
#print axioms oracleProgram_exact
#print axioms oracleProgram_value
end AspisR1PublicPreparation.PreparedHashCode
