import R1QuerySampler

/-! Connect the generic paired sampler to the existing eight-step Q22
first-read result. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.QuerySamplerBridge

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.QueryStateList

variable {M Cv : Type} {L : Nat} (p : Params M Cv L) (H : Addr L → State)

def sampler (p : Params M Cv L) (a : Addr L) :
    Sampler (Addr L) State AspisV8R19.Q22SamplerProgram.Result :=
  .ask a fun s =>
    QuerySampler.chain p
      (fun bs xs => Q22.scanOut 8 Q22.q0 bs xs s) 8 s [] []

theorem output (a : Addr L) :
    (eval H (sampler p a).toProgram).2 =
      QueryFirstRead.result p H (QuerySampler.state p H (H a)) := by
  simpa [sampler, QueryFirstRead.result, QueryStateList.blocks, QueryStateList.advances] using
    (QuerySampler.chain_out p H
      (fun bs xs => Q22.scanOut 8 Q22.q0 bs xs) 8 (H a) [] [])

theorem reads_absorb (a : Addr L) :
    a ∈ (eval H (sampler p a).toProgram).1.map Prod.fst := by
  simp [sampler, Sampler.toProgram, eval]

theorem reads_pairs (a : Addr L) : ∀ k, k < 8 →
    squeezeA p (QuerySampler.state p H (H a) k) ∈
        (eval H (sampler p a).toProgram).1.map Prod.fst ∧
      advanceA p (QuerySampler.state p H (H a) k) ∈
        (eval H (sampler p a).toProgram).1.map Prod.fst := by
  intro k hk
  have h := QuerySampler.chain_reads p H
    (fun bs xs => Q22.scanOut 8 Q22.q0 bs xs) 8 (H a) [] [] k hk
  simpa [sampler, Sampler.toProgram, eval, List.map_cons, List.mem_cons] using
    And.intro (Or.inr h.1) (Or.inr h.2)

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
