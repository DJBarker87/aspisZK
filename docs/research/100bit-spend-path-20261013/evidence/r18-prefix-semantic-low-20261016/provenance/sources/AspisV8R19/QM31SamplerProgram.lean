import AspisV8R19.SamplerWords

/-! Source-shaped bounded QM31 sampling. The cursor is shared across the four
limbs; each limb resets its own eight-attempt budget. A new top-level call
always squeezes a new block and discards the prior call's unused suffix. -/
set_option autoImplicit false
namespace AspisV8R19.QM31SamplerProgram
open DuplexFrames SourceDuplexStep SourceOraclePrograms SamplerWords
open MemoizedProgramLaw OracleProgramOps

structure Cursor where
  state : State
  block : State
  index : Fin 9

def readProgram (c : Cursor) : Program Bytes State (Nat × Cursor) :=
  if h : c.index.val = 8 then
    bind (squeezeProgram c.state) (fun p =>
      .done (word p.1 0,⟨p.2,p.1,1⟩))
  else .done (word c.block ⟨c.index.val,by have := c.index.isLt; omega⟩,
    ⟨c.state,c.block,⟨c.index.val+1,by have := c.index.isLt; omega⟩⟩)

def readRun (H : Bytes → State) (c : Cursor) : View Bytes State (Nat × Cursor) :=
  if h : c.index.val = 8 then
    let p := step H c.state
    (calls H c.state,(word p.1 0,⟨p.2,p.1,1⟩))
  else ([],(word c.block ⟨c.index.val,by have := c.index.isLt; omega⟩,
    ⟨c.state,c.block,⟨c.index.val+1,by have := c.index.isLt; omega⟩⟩))

theorem read_exact (H : Bytes → State) (c : Cursor) :
    eval H (readProgram c) = readRun H c := by
  by_cases h : c.index.val = 8 <;>
    simp [readProgram,readRun,h,eval_bind,squeeze_eval,eval]

theorem read_call_count (H : Bytes → State) (c : Cursor) :
    (readRun H c).1.length = if c.index.val = 8 then 2 else 0 := by
  by_cases h : c.index.val = 8 <;> simp [readRun,h,calls]

def limbProgram : Nat → Cursor → Program Bytes State (Option Nat × Cursor)
  | 0,c => .done (none,c)
  | n+1,c => bind (readProgram c) (fun r =>
      if masked 31 r.1 = 2147483647 then limbProgram n r.2
      else .done (some (masked 31 r.1),r.2))

def limbRun (H : Bytes → State) : Nat → Cursor → View Bytes State (Option Nat × Cursor)
  | 0,c => ([],(none,c))
  | n+1,c =>
      let r := readRun H c
      if masked 31 r.2.1 = 2147483647 then
        let tail := limbRun H n r.2.2
        (r.1 ++ tail.1,tail.2)
      else (r.1,(some (masked 31 r.2.1),r.2.2))

theorem limb_exact (H : Bytes → State) (n : Nat) (c : Cursor) :
    eval H (limbProgram n c) = limbRun H n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      simp only [limbProgram,eval_bind,read_exact,limbRun]
      split_ifs <;> simp [ih,eval]

theorem accepted_limb_canonical (H : Bytes → State) (n : Nat) (c : Cursor)
    (a : Nat) (h : (limbRun H n c).2.1 = some a) : a < 2147483647 := by
  induction n generalizing c with
  | zero => simp [limbRun] at h
  | succ n ih =>
      simp only [limbRun] at h
      split_ifs at h with reject
      · exact ih _ h
      · have ha : masked 31 (readRun H c).2.1 = a := Option.some.inj h
        have hb := masked_bound 31 (readRun H c).2.1
        change masked 31 (readRun H c).2.1 < 2147483648 at hb
        omega

def limbsProgram : Nat → Cursor → Program Bytes State (Option (List Nat) × Cursor)
  | 0,c => .done (some [],c)
  | n+1,c => bind (limbProgram 8 c) (fun r => match r.1 with
      | none => .done (none,r.2)
      | some a => bind (limbsProgram n r.2) (fun tail =>
          .done (tail.1.map (a::·),tail.2)))

def limbsRun (H : Bytes → State) : Nat → Cursor → View Bytes State (Option (List Nat) × Cursor)
  | 0,c => ([],(some [],c))
  | n+1,c =>
      let r := limbRun H 8 c
      match r.2.1 with
      | none => (r.1,(none,r.2.2))
      | some a =>
          let tail := limbsRun H n r.2.2
          (r.1 ++ tail.1,(tail.2.1.map (a::·),tail.2.2))

theorem limbs_exact (H : Bytes → State) (n : Nat) (c : Cursor) :
    eval H (limbsProgram n c) = limbsRun H n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      simp only [limbsProgram,eval_bind,limb_exact,limbsRun]
      cases h : (limbRun H 8 c).2.1 <;> simp [h,eval,eval_bind,ih]

def challengeProgram (s : State) : Program Bytes State (Option (List Nat) × State) :=
  bind (squeezeProgram s) (fun p =>
    bind (limbsProgram 4 ⟨p.2,p.1,0⟩) (fun r => .done (r.1,r.2.state)))

def challengeRun (H : Bytes → State) (s : State) : View Bytes State (Option (List Nat) × State) :=
  let p := step H s
  let tail := limbsRun H 4 ⟨p.2,p.1,0⟩
  (calls H s ++ tail.1,(tail.2.1,tail.2.2.state))

theorem challenge_exact (H : Bytes → State) (s : State) :
    eval H (challengeProgram s) = challengeRun H s := by
  simp [challengeProgram,challengeRun,eval_bind,squeeze_eval,limbs_exact,eval]

#print axioms read_exact
#print axioms read_call_count
#print axioms limb_exact
#print axioms accepted_limb_canonical
#print axioms limbs_exact
#print axioms challenge_exact
end AspisV8R19.QM31SamplerProgram
