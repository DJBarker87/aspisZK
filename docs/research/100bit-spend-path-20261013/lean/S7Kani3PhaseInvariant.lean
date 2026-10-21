import S7Kani2OwnedRowRefinement
set_option autoImplicit false
namespace S7Kani3PhaseInvariant
open AspisR1BatchedFoldSourceStep

def Phase (terms raw : Nat) : Prop := raw < 2^34+(terms%4)*productCap

/-- The exact periodic-flush invariant is inductive at every query, including
checkpoints in the middle of a four-query group. -/
theorem push_phase (terms raw product : Nat) (hr : Phase terms raw)
    (hp : product ≤ productCap) :
    raw+product<2^64 ∧ Phase (terms+1) (sourcePush terms raw product) := by
  have ht : terms%4<4 := Nat.mod_lt _ (by decide)
  have hs : raw+product<2^64 := by
    dsimp [Phase,productCap] at hr hp
    omega
  refine ⟨hs,?_⟩
  unfold sourcePush
  split
  · have hb := fold_lt_two34 hs
    have hz : (terms+1)%4=0 := by omega
    simpa [Phase,hz] using hb
  · have hn : (terms+1)%4=terms%4+1 := by omega
    dsimp [Phase] at hr ⊢
    rw [hn,Nat.add_mul,Nat.one_mul]
    omega

def run : Nat → Nat → List Nat → Nat
 | _,raw,[] => raw
 | terms,raw,p::ps => run (terms+1) (sourcePush terms raw p) ps

/-- Complete outer query induction. This proves phase safety, rather than
assuming that each reached state continues to satisfy it. -/
theorem run_phase (products : List Nat) (terms raw : Nat)
    (hr : Phase terms raw) (hp : ∀ p∈products,p ≤ productCap) :
    Phase (terms+products.length) (run terms raw products) := by
  induction products generalizing terms raw with
  | nil => simpa [run] using hr
  | cons p ps ih =>
      have hs := push_phase terms raw p hr (hp p (by simp))
      have hi := ih (terms+1) (sourcePush terms raw p) hs.2
        (fun x hx => hp x (by simp [hx]))
      simpa [run,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hi

/-- Raw residues agree with the unreduced sum for any starting phase and any
number of queries. No canonicalisation or overflow assumption is needed for
this mathematical congruence. -/
theorem run_congruence (products : List Nat) (terms raw : Nat) :
    run terms raw products % modulus=(raw+products.sum)%modulus := by
  induction products generalizing terms raw with
  | nil => simp [run]
  | cons p ps ih =>
      simp only [run,ih,List.sum_cons]
      calc
        (sourcePush terms raw p+ps.sum)%modulus =
            ((sourcePush terms raw p)%modulus+ps.sum%modulus)%modulus := Nat.add_mod _ _ _
        _ = ((raw+p)%modulus+ps.sum%modulus)%modulus := by rw [sourcePush_mod]
        _ = (raw+(p+ps.sum))%modulus := by rw [←Nat.add_mod]; rw [Nat.add_assoc]

/-- Compose two checkpoint intervals without resetting the terms phase. -/
theorem checkpoint_composition (first second : List Nat) (terms raw : Nat) :
    run terms raw (first++second)=
      run (terms+first.length) (run terms raw first) second := by
  induction first generalizing terms raw with
  | nil => simp [run]
  | cons p ps ih =>
      simpa [run,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        ih (terms+1) (sourcePush terms raw p)

#print axioms push_phase
#print axioms run_phase
#print axioms run_congruence
#print axioms checkpoint_composition
end S7Kani3PhaseInvariant
