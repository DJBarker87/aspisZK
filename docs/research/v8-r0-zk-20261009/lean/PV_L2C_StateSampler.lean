import PV_L2C_SampleCanonical
import PV_L2C_DecodeRange
import R1Z.PV_Src_CompilerTactic
set_option autoImplicit false
namespace PV_L2C_StateSampler
open Aeneas Aeneas.Std Result PV_L2C_M31
inductive Failure where
  | exhausted

/-- Owned stateful source cut. Next-word calls, exhausted state and every
source Result failure are retained; no distribution law is assumed. -/
def scalar {S : Type} (next : S → Result (word × S)) : Nat → S → Result (Except Failure word × S)
  | 0,s => ok (.error .exhausted,s)
  | n+1,s => do
    let (raw,s1) ← next s
    let candidate := raw &&& BitVec.ofNat 32 p
    if candidate.toNat < p then ok (.ok candidate,s1) else scalar next n s1

theorem canonical_result {S : Type} (next : S → Result (word × S)) (fuel : Nat)
    (s s1 : S) (v : word) (h : scalar next fuel s = ok (.ok v,s1)) : canonical v := by
  induction fuel generalizing s with
  | zero => cases h
  | succ n ih =>
    rw [scalar] at h
    pv_peel h with pair hp
    rcases pair with ⟨raw,after⟩
    dsimp only at h
    split at h
    · cases h;assumption
    · exact ih after h
#print axioms canonical_result

abbrev Step (S A : Type) := S → Result (Except Failure A × S)

def bind {S A B : Type} (first : Step S A) (thenStep : A → Step S B) : Step S B := fun s => do
  let (result,s1) ← first s
  match result with
  | .error e => ok (.error e,s1)
  | .ok a => thenStep a s1

def pure {S A : Type} (a : A) : Step S A := fun s => ok (.ok a,s)

theorem bind_returned {S A B : Type} (first : Step S A) (thenStep : A → Step S B)
    (s outState : S) (out : B) (h : bind first thenStep s = ok (.ok out,outState)) :
    ∃ a s1, first s = ok (.ok a,s1) ∧ thenStep a s1 = ok (.ok out,outState) := by
  unfold bind at h
  pv_peel h with pair hp
  rcases pair with ⟨result,s1⟩
  cases result with
  | error e => cases h
  | ok a => exact ⟨a,s1,hp,h⟩
#print axioms bind_returned

def secure {S : Type} (next : S → Result (word × S)) (fuel : Nat) : Step S PV_L2C_NativeQ.Q :=
  bind (scalar next fuel) (fun a => bind (scalar next fuel) (fun b =>
    bind (scalar next fuel) (fun c => bind (scalar next fuel) (fun d =>
      pure (PV_L2C_SampleCanonical.tuple a b c d)))))

theorem secure_result {S : Type} (next : S → Result (word × S)) (fuel : Nat)
    (s s1 : S) (q : PV_L2C_NativeQ.Q) (h : secure next fuel s = ok (.ok q,s1)) :
    PV_L2C_NativeQ.Canonical q := by
  unfold secure at h
  obtain ⟨a,sa,ha,h⟩ := bind_returned _ _ _ _ _ h
  obtain ⟨b,sb,hb,h⟩ := bind_returned _ _ _ _ _ h
  obtain ⟨c,sc,hc,h⟩ := bind_returned _ _ _ _ _ h
  obtain ⟨d,sd,hd,h⟩ := bind_returned _ _ _ _ _ h
  cases h
  exact PV_L2C_SampleCanonical.tuple_canonical _ _ _ _
    (canonical_result next fuel s sa a ha) (canonical_result next fuel sa sb b hb)
    (canonical_result next fuel sb sc c hc) (canonical_result next fuel sc s1 d hd)
#print axioms secure_result
end PV_L2C_StateSampler
