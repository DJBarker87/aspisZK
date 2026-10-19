import R1InitialSamplerLaw
import R1ReseedSamplerLaw

/-! Ordinary sampler representations for plain, initial, and reseeded duplex
rounds, with their first-read traces and independent-answer laws. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.DuplexSamplers

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

variable {M Cv C : Type} {L : Nat}

def plain (p : Params M Cv L) (a : Addr L) (i : Nat)
    (G : Chal Cv → C) : Sampler (Addr L) State C :=
  .ask a fun s => .ask (squeezeA p s) fun b => .ask (advanceA p s) fun x =>
    .done (G (p.σ i b, x))

def initial (p : Params M Cv L) (init : Addr L) (begin : State → Addr L)
    (i : Nat) (G : Chal Cv → C) : Sampler (Addr L) State C :=
  .ask init fun s => .ask (begin s) fun a => .ask (squeezeA p a) fun b =>
    .ask (advanceA p a) fun x => .done (G (p.σ i b, x))

def reseeded (p : Params M Cv L) (a : Addr L) (reseed : State → Addr L)
    (i : Nat) (G : Chal Cv → C) : Sampler (Addr L) State C :=
  .ask a fun s => .ask (squeezeA p s) fun b => .ask (advanceA p s) fun x =>
    .ask (reseed x) fun y => .done (G (p.σ i b, y))

theorem plain_eval (p : Params M Cv L) (a : Addr L) (i : Nat)
    (G : Chal Cv → C) (H : Addr L → State) :
    eval H (plain p a i G).toProgram =
      ([(a, H a), (squeezeA p (H a), H (squeezeA p (H a))),
        (advanceA p (H a), H (advanceA p (H a)))],
        G (p.σ i (H (squeezeA p (H a))), H (advanceA p (H a)))) := rfl

theorem initial_eval (p : Params M Cv L) (init : Addr L)
    (begin : State → Addr L) (i : Nat) (G : Chal Cv → C)
    (H : Addr L → State) :
    eval H (initial p init begin i G).toProgram =
      ([(init, H init), (begin (H init), H (begin (H init))),
        (squeezeA p (H (begin (H init))), H (squeezeA p (H (begin (H init))))),
        (advanceA p (H (begin (H init))), H (advanceA p (H (begin (H init)))))],
        G (p.σ i (H (squeezeA p (H (begin (H init))))),
          H (advanceA p (H (begin (H init)))))) := rfl

theorem reseeded_eval (p : Params M Cv L) (a : Addr L)
    (reseed : State → Addr L) (i : Nat) (G : Chal Cv → C)
    (H : Addr L → State) :
    eval H (reseeded p a reseed i G).toProgram =
      ([(a, H a), (squeezeA p (H a), H (squeezeA p (H a))),
        (advanceA p (H a), H (advanceA p (H a))),
        (reseed (H (advanceA p (H a))), H (reseed (H (advanceA p (H a)))))],
        G (p.σ i (H (squeezeA p (H a))),
          H (reseed (H (advanceA p (H a)))))) := rfl

theorem plain_law (p : Params M Cv L) (a : Addr L) (i : Nat)
    (G : Chal Cv → C) (obs : C → ℚ) :
    independentMean (plain p a i G).toProgram (fun w => obs w.2) =
      mean (fun b => mean (fun x => obs (G (p.σ i b, x)))) := by
  simp only [plain, Sampler.toProgram, independentMean, mean_const]

theorem initial_law (p : Params M Cv L) (init : Addr L)
    (begin : State → Addr L) (i : Nat) (G : Chal Cv → C) (obs : C → ℚ) :
    independentMean (initial p init begin i G).toProgram (fun w => obs w.2) =
      mean (fun b => mean (fun x => obs (G (p.σ i b, x)))) := by
  simp only [initial, Sampler.toProgram, independentMean, mean_const]

theorem reseeded_law (p : Params M Cv L) (a : Addr L)
    (reseed : State → Addr L) (i : Nat) (G : Chal Cv → C) (obs : C → ℚ) :
    independentMean (reseeded p a reseed i G).toProgram (fun w => obs w.2) =
      mean (fun b => mean (fun y => obs (G (p.σ i b, y)))) := by
  simp only [reseeded, Sampler.toProgram, independentMean, mean_const]

theorem plain_own_matches (p : Params M Cv L) (a : Addr L) (i : Nat)
    (G : Chal Cv → C) (obs : C → ℚ) :
    blaw (fun x bs => G (p.σ i (bs.headD default), x)) obs
      (QueryNextLaw.own p a) [] =
        independentMean (plain p a i G).toProgram (fun w => obs w.2) := by
  rw [QueryNextLaw.own_law, plain_law]

theorem initial_own_matches (p : Params M Cv L) (init : Addr L)
    (begin : State → Addr L) (i : Nat) (G : Chal Cv → C) (obs : C → ℚ) :
    blaw (fun x bs => G (p.σ i (bs.headD default), x)) obs
      (InitialSamplerLaw.own p init begin) [] =
        independentMean (initial p init begin i G).toProgram (fun w => obs w.2) := by
  rw [InitialSamplerLaw.own_law, initial_law]

theorem reseeded_own_matches (p : Params M Cv L) (a : Addr L)
    (reseed : State → Addr L) (i : Nat) (G : Chal Cv → C) (obs : C → ℚ) :
    blaw (fun y bs => G (p.σ i (bs.headD default), y)) obs
      (ReseedSamplerLaw.own p a reseed) [] =
        independentMean (reseeded p a reseed i G).toProgram (fun w => obs w.2) := by
  rw [ReseedSamplerLaw.own_law, reseeded_law]

#print axioms plain_eval
#print axioms initial_eval
#print axioms reseeded_eval
#print axioms plain_law
#print axioms initial_law
#print axioms reseeded_law
#print axioms plain_own_matches
#print axioms initial_own_matches
#print axioms reseeded_own_matches

end AspisR1.DuplexSamplers
end
