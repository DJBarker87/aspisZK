import S1PreparedOracleProgramLawsV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedBudget
open Aeneas Aeneas.Std Result
open PreparedHashCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw

/-- Structural bound on every response-driven path, including rejected
prefixes. It counts every digest node, including repeated addresses. -/
def bounded {A : Type} : Nat → Code A → Prop
  | _, .done _ => True
  | n, .step _ k => ∀ a,bounded n (k a)
  | n, .digest _ _ _ k => 0<n ∧ ∀ a,bounded (n-1) (k a)

theorem mono {A : Type} (p : Code A) (n m : Nat) (le : n≤m) (h : bounded n p) : bounded m p := by
  induction p generalizing n m with
  | done a => trivial
  | step r k ih => intro a;exact ih a n m le (h a)
  | digest D hash parts k ih =>
    refine ⟨by omega,?_⟩
    intro a
    exact ih a (n-1) (m-1) (by omega) (h.2 a)

theorem bind_bound {A B : Type} (p : Code A) (k : A → Code B) (m n : Nat)
    (hp : bounded m p) (hk : ∀ a,bounded n (k a)) : bounded (m+n) (p >>= k) := by
  induction p generalizing m with
  | done a => exact mono _ n (m+n) (by omega) (hk a)
  | step r next ih => intro a;exact ih a m (hp a)
  | digest D hash parts next ih =>
    refine ⟨by omega,?_⟩
    intro a
    have rest := ih a (m-1) (hp.2 a)
    have size : m-1+n=m+n-1 := by omega
    simpa only [size] using rest

theorem then_bound {A B : Type} {p : Code A} {k : A → Code B} {total cost : Nat}
    (covered : cost≤total) (hp : bounded cost p)
    (hk : ∀ a,bounded (total-cost) (k a)) : bounded total (p >>= k) := by
  have h := bind_bound p k cost (total-cost) hp hk
  have same : cost+(total-cost)=total := by omega
  simpa only [same] using h

theorem pure_bound {A : Type} (n : Nat) (a : A) : bounded n (pure a : Code A) := trivial

theorem lift_bound {A : Type} (n : Nat) (r : Result A) : bounded n (monadLift r : Code A) := by
  intro a
  trivial

theorem lift_bind {A B : Type} (r : Result A) (k : A → Code B) (n : Nat)
    (hk : ∀ a,bounded n (k a)) : bounded n ((monadLift r : Code A) >>= k) := hk

theorem digest_bound {Hash : Type} (D : aspis_core.Digest32 Hash) (hash : Hash)
    (parts : Slice (Slice U8)) : bounded 1 (effects.digest D hash parts) := ⟨by decide,fun _ => trivial⟩

/-- Actual ordered Program log, with no acceptance, freshness or OracleValid premise. -/
theorem count {A : Type} (p : Code A) (H : Bytes → State) (n : Nat) (h : bounded n p) :
    (eval H (oracleProgram p)).1.length≤n := by
  induction p generalizing n with
  | done a => exact Nat.zero_le n
  | step r k ih =>
    cases r with
    | ok a => exact ih a n (h a)
    | fail e => exact Nat.zero_le n
    | div => exact Nat.zero_le n
  | digest D hash parts k ih =>
    have rest := ih (encodeState (H (flatten parts))) (n-1) (h.2 _)
    change 1+(eval H (oracleProgram (k (encodeState (H (flatten parts)))))).1.length≤n
    omega

#print axioms bind_bound
#print axioms count
end AspisR1PublicPreparation.PreparedBudget
