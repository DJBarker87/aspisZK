import AspisV8R19.SamplerRawCursorBridge

/-! Raw-word view of the deterministic QM31 sampler execution.

The definitions below duplicate only the source recursion, replacing each
byte-block word projection by `stateRawEquiv`.  The equalities are
representation equalities; they assert no oracle or distribution property.
-/
set_option autoImplicit false
namespace AspisV8R19.SamplerRawExecutionBridge

open DuplexFrames SourceDuplexStep SamplerWords
open AspisV8R19.QM31SamplerProgram
open AspisV8R19.SamplerRawStateRepresentation
open AspisV8R19.SamplerRawCursorBridge
open MemoizedProgramLaw

def rawReadRun (H : Bytes → State) (c : Cursor) :
    View Bytes State (Nat × Cursor) :=
  if h : c.index.val = 8 then
    let p := step H c.state
    (calls H c.state,
      (((stateRawEquiv p.1) 0).val, ⟨p.2,p.1,1⟩))
  else
    ([],
      (((stateRawEquiv c.block) ⟨c.index.val, by omega⟩).val,
        ⟨c.state,c.block,⟨c.index.val+1, by omega⟩⟩))

def rawLimbRun (H : Bytes → State) : Nat → Cursor →
    View Bytes State (Option Nat × Cursor)
  | 0,c => ([],(none,c))
  | n+1,c =>
      let r := rawReadRun H c
      if masked 31 r.2.1 = 2147483647 then
        let tail := rawLimbRun H n r.2.2
        (r.1 ++ tail.1,tail.2)
      else (r.1,(some (masked 31 r.2.1),r.2.2))

def rawLimbsRun (H : Bytes → State) : Nat → Cursor →
    View Bytes State (Option (List Nat) × Cursor)
  | 0,c => ([],(some [],c))
  | n+1,c =>
      let r := rawLimbRun H 8 c
      match r.2.1 with
      | none => (r.1,(none,r.2.2))
      | some a =>
          let tail := rawLimbsRun H n r.2.2
          (r.1 ++ tail.1,(tail.2.1.map (a::·),tail.2.2))

def rawChallengeRun (H : Bytes → State) (s : State) :
    View Bytes State (Option (List Nat) × State) :=
  let p := step H s
  let tail := rawLimbsRun H 4 ⟨p.2,p.1,0⟩
  (calls H s ++ tail.1,(tail.2.1,tail.2.2.state))

theorem rawReadRun_eq (H : Bytes → State) (c : Cursor) :
    rawReadRun H c = readRun H c := by
  by_cases h : c.index.val = 8
  · rw [readRun_rollover H c h]
    simp [rawReadRun, h, stateRawEquiv_word]
  · have hlt : c.index.val < 8 := by omega
    rw [readRun_before_rollover H c hlt]
    simp [rawReadRun, h, stateRawEquiv_word]

theorem rawLimbRun_eq (H : Bytes → State) (n : Nat) (c : Cursor) :
    rawLimbRun H n c = limbRun H n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      simp only [rawLimbRun, limbRun]
      rw [rawReadRun_eq]
      split_ifs with h
      · simp [ih]
      · rfl

theorem rawLimbsRun_eq (H : Bytes → State) (n : Nat) (c : Cursor) :
    rawLimbsRun H n c = limbsRun H n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      simp only [rawLimbsRun, limbsRun]
      rw [rawLimbRun_eq]
      cases h : (limbRun H 8 c).2.1 with
      | none => simp
      | some a => simp [ih]

theorem rawChallengeRun_eq (H : Bytes → State) (s : State) :
    rawChallengeRun H s = challengeRun H s := by
  simp only [rawChallengeRun, challengeRun]
  rw [rawLimbsRun_eq]

#print axioms rawReadRun_eq
#print axioms rawLimbRun_eq
#print axioms rawLimbsRun_eq
#print axioms rawChallengeRun_eq
end AspisV8R19.SamplerRawExecutionBridge
