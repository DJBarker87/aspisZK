import R1ReseedTrace

/-! The row-ending sampler has the original challenge law while carrying
the reseeded next state. This is a sampler interface, not the full R1 instance. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.ReseedRound
open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

def sampler (p : Params M Cv L) (a : Addr L) (reseed : State → Addr L)
    (i : Nat) : Sampler (Addr L) State (Chal Cv) :=
  .ask a fun s => .ask (squeezeA p s) fun b =>
    .ask (advanceA p s) fun x => .ask (reseed x) fun y => .done (p.σ i b, y)

theorem firstCell_sampler (p : Params M Cv L) (a : Addr L)
    (reseed : State → Addr L) (i : Nat) :
    firstCell (sampler p a reseed i) = some a := rfl

theorem sampler_eval (p : Params M Cv L) (a : Addr L)
    (reseed : State → Addr L) (i : Nat) (H : Addr L → State) :
    eval H (sampler p a reseed i).toProgram =
      ([(a, H a), (squeezeA p (H a), H (squeezeA p (H a))),
        (advanceA p (H a), H (advanceA p (H a))),
        (reseed (H (advanceA p (H a))), H (reseed (H (advanceA p (H a)))))],
       (p.σ i (H (squeezeA p (H a))), H (reseed (H (advanceA p (H a)))))) := rfl

theorem sampler_law (p : Params M Cv L) (a : Addr L)
    (reseed : State → Addr L) (i : Nat) (obs : Chal Cv → ℚ) :
    independentMean (sampler p a reseed i).toProgram (fun w => obs w.2) =
      mean (fun b => mean (fun y => obs (p.σ i b, y))) := by
  simp only [sampler, Sampler.toProgram, independentMean, mean_const]

theorem own_matches_sampler (p : Params M Cv L) (a : Addr L)
    (reseed : State → Addr L) (i : Nat) (obs : Chal Cv → ℚ) :
    blaw (fun y bs => (p.σ i (bs.headD default), y)) obs
        (ReseedSamplerLaw.own p a reseed) [] =
      independentMean (sampler p a reseed i).toProgram (fun w => obs w.2) := by
  rw [sampler_law]
  exact ReseedSamplerLaw.own_law p a reseed i id obs

theorem same_challenge_law {X : Type} (p : Params M Cv L) (a : Addr L)
    (reseed : State → Addr L) (i : Nat) (pre : Prefix X M (Chal Cv))
    (m : M) (bad : Chal Cv → Prop) :
    independentMean (sampler p a reseed i).toProgram (fun w => indicator (bad w.2)) =
      independentMean (samp p i pre m).toProgram (fun w => indicator (bad w.2)) := by
  rw [sampler_law, samp_mean]

#print axioms firstCell_sampler
#print axioms sampler_eval
#print axioms sampler_law
#print axioms own_matches_sampler
#print axioms same_challenge_law
end AspisR1.ReseedRound
end
