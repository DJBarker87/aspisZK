import R1QueryNextLaw

/-! Independent-answer law for the initial duplex sampler, together with its
ordinary sampler representation. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.InitialSamplerLaw

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

def own (p : Params M Cv L) (init : Addr L) (begin : State → Addr L) :
    BS (Addr L) State State :=
  .ask init fun s => .ask (begin s) fun a =>
    .spawn (squeezeA p a) (.ask (advanceA p a) fun x => .done x)

def sampler (p : Params M Cv L) (init : Addr L) (begin : State → Addr L)
    (i : Nat) : Sampler (Addr L) State (Chal Cv) :=
  .ask init fun s => .ask (begin s) fun a =>
    .ask (squeezeA p a) fun b => .ask (advanceA p a) fun x =>
      .done (p.σ i b, x)

theorem own_law {C : Type} (p : Params M Cv L) (init : Addr L)
    (begin : State → Addr L) (i : Nat) (G : Chal Cv → C)
    (obs : C → ℚ) :
    blaw (fun x bs => G (p.σ i (bs.headD default), x)) obs
      (own p init begin) [] =
      mean (fun b => mean (fun x => obs (G (p.σ i b, x)))) := by
  simp only [own, blaw, pmean, List.nil_append, List.headD_cons]
  rw [mean_const, mean_const, mean_comm]

theorem firstCell (p : Params M Cv L) (init : Addr L)
    (begin : State → Addr L) (i : Nat) :
    firstCell (sampler p init begin i) = some init := rfl

theorem sampler_eval (p : Params M Cv L) (init : Addr L)
    (begin : State → Addr L) (i : Nat) (H : Addr L → State) :
    eval H (sampler p init begin i).toProgram =
      ([(init, H init),
        (begin (H init), H (begin (H init))),
        (squeezeA p (H (begin (H init))), H (squeezeA p (H (begin (H init))))),
        (advanceA p (H (begin (H init))), H (advanceA p (H (begin (H init)))))],
       (p.σ i (H (squeezeA p (H (begin (H init))))),
        H (advanceA p (H (begin (H init)))))) := rfl

theorem sampler_law {C : Type} (p : Params M Cv L) (init : Addr L)
    (begin : State → Addr L) (i : Nat) (G : Chal Cv → C)
    (obs : C → ℚ) :
    independentMean (sampler p init begin i).toProgram (fun w => obs (G w.2)) =
      mean (fun b => mean (fun x => obs (G (p.σ i b, x)))) := by
  simp only [sampler, Sampler.toProgram, independentMean, mean_const]

theorem own_matches_sampler {C : Type} (p : Params M Cv L) (init : Addr L)
    (begin : State → Addr L) (i : Nat) (G : Chal Cv → C)
    (obs : C → ℚ) :
    blaw (fun x bs => G (p.σ i (bs.headD default), x)) obs
      (own p init begin) [] =
      independentMean (sampler p init begin i).toProgram (fun w => obs (G w.2)) := by
  rw [own_law, sampler_law]

#print axioms own_law
#print axioms firstCell
#print axioms sampler_eval
#print axioms sampler_law
#print axioms own_matches_sampler

end AspisR1.InitialSamplerLaw
end
