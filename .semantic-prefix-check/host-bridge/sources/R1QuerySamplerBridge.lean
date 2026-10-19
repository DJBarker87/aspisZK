import R1QuerySampler

/-! Connect the generic paired sampler to the existing eight-step Q22
first-read result. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.QuerySamplerBridge

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.QueryStateList

variable {M Cv : Type} {L : Nat} (p : Params M Cv L) (H : Addr L → State)

def sampler {C : Type} (p : Params M Cv L) (a : Addr L)
    (G : AspisV8R19.Q22SamplerProgram.Result → C) : Sampler (Addr L) State C :=
  .ask a fun s =>
    QuerySampler.chain p
      (fun bs xs => G (Q22.scanOut 8 Q22.q0 bs xs s)) 8 s [] []

theorem output {C : Type} (a : Addr L)
    (G : AspisV8R19.Q22SamplerProgram.Result → C) :
    (eval H (sampler p a G).toProgram).2 =
      G (QueryFirstRead.result p H (QuerySampler.state p H (H a))) := by
  simp only [sampler, Sampler.toProgram, eval, QuerySampler.state]
  rw [QuerySampler.chain_out]
  rfl

theorem reads_absorb {C : Type} (a : Addr L)
    (G : AspisV8R19.Q22SamplerProgram.Result → C) :
    a ∈ (eval H (sampler p a G).toProgram).1.map Prod.fst := by
  simp [sampler, Sampler.toProgram, eval]

theorem reads_pairs {C : Type} (a : Addr L)
    (G : AspisV8R19.Q22SamplerProgram.Result → C) : ∀ k, k < 8 →
    squeezeA p (QuerySampler.state p H (H a) k) ∈
        (eval H (sampler p a G).toProgram).1.map Prod.fst ∧
      advanceA p (QuerySampler.state p H (H a) k) ∈
        (eval H (sampler p a G).toProgram).1.map Prod.fst := by
  intro k hk
  have h := QuerySampler.chain_reads p H
    (fun bs xs => G (Q22.scanOut 8 Q22.q0 bs xs (H a))) 8 (H a) [] [] k hk
  change
    squeezeA p (QuerySampler.state p H (H a) k) ∈
        ((a, H a) :: (eval H (QuerySampler.chain p
          (fun bs xs => G (Q22.scanOut 8 Q22.q0 bs xs (H a))) 8 (H a) [] []).toProgram).1).map Prod.fst ∧
      advanceA p (QuerySampler.state p H (H a) k) ∈
        ((a, H a) :: (eval H (QuerySampler.chain p
          (fun bs xs => G (Q22.scanOut 8 Q22.q0 bs xs (H a))) 8 (H a) [] []).toProgram).1).map Prod.fst
  simp only [List.map_cons, List.mem_cons]
  exact ⟨Or.inr h.1, Or.inr h.2⟩

theorem state_step (s : State) (n : Nat) :
    QuerySampler.state p H s (n + 1) =
      H (advanceA p (QuerySampler.state p H s n)) := rfl

theorem state_initial (s : State) : QuerySampler.state p H s 0 = s := rfl

#print axioms output
#print axioms reads_absorb
#print axioms reads_pairs
#print axioms state_step
#print axioms state_initial

end AspisR1.QuerySamplerBridge
end
