import F3J_SamplerRun
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_QueryLog
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def issued {M Cv : Type} {L : Nat} (p : Params M Cv L) (H : Addr L → State) :
    Nat → State → List (Addr L × State)
  | 0,_ => []
  | n+1,s => (squeezeA p s,H (squeezeA p s))::(advanceA p s,H (advanceA p s))::
      issued p H n (H (advanceA p s))

theorem chain {M Cv C : Type} {L : Nat} (p : Params M Cv L) (H : Addr L → State)
    (out : List State → List State → C) (n : Nat) (s : State) (bs xs : List State) :
    (eval H (QuerySampler.chain p out n s bs xs).toProgram).1=issued p H n s := by
  induction n generalizing s bs xs with
  | zero => rfl
  | succ n ih =>
    change (squeezeA p s,H (squeezeA p s))::(advanceA p s,H (advanceA p s))::
      (eval H (QuerySampler.chain p out n (H (advanceA p s))
        (bs++[H (squeezeA p s)]) (xs++[H (advanceA p s)])).toProgram).1=_
    rw [ih]
    rfl

theorem length {M Cv : Type} {L : Nat} (p : Params M Cv L) (H : Addr L → State)
    (n : Nat) (s : State) : (issued p H n s).length=2*n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [issued,List.length_cons,ih];omega

theorem sampler {M Cv C : Type} {L : Nat} (p : Params M Cv L) (H : Addr L → State)
    (a : Addr L) (out : AspisV8R19.Q22SamplerProgram.Result → C) :
    (eval H (QuerySamplerBridge.sampler p a out).toProgram).1=
      (a,H a)::issued p H 8 (H a) := by
  change (a,H a)::(eval H (QuerySampler.chain p
    (fun bs xs => out (Q22.scanOut 8 Q22.q0 bs xs (H a))) 8 (H a) [] []).toProgram).1=_
  rw [chain]

#print axioms chain
#print axioms length
#print axioms sampler
end AspisR1.F3J_QueryLog
end
