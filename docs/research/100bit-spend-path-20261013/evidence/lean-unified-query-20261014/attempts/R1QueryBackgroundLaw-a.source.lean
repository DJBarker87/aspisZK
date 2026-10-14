import R1QueryBackgroundChain
import R1QuerySampler
import R0C.V3.DuplexQ

/-! Exact averaging identities for the generic query background chain and
its evaluated paired-answer sampler. These are structural laws only. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.QueryBackgroundLaw

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

theorem blaw_chainBS (p : Params M Cv L) {C : Type}
    (G : List State → List State → C) (obs : C → ℚ) :
    ∀ n s xs pre,
      blaw G obs (QueryBackgroundChain.chainBS p n s xs) pre =
        pmean (fun as => Q22.chainE
          (fun bs ys => obs (G (xs ++ ys) (as ++ bs))) n) pre := by
  intro n
  induction n with
  | zero =>
      intro s xs pre
      simp only [QueryBackgroundChain.chainBS, blaw, Q22.chainE, List.append_nil]
  | succ n ih =>
      intro s xs pre
      simp only [QueryBackgroundChain.chainBS, blaw]
      simp only [ih, R0C.V3.DQ.pmean_snoc]
      rw [← R0C.V3.pmean_mean_comm pre (fun x as => mean (fun b => Q22.chainE
        (fun bs ys => obs (G (xs ++ [x] ++ ys) (as ++ [b] ++ bs))) n))]
      apply congrArg (fun F => pmean F pre)
      funext as
      simp only [Q22.chainE]
      rw [mean_comm]
      simp only [List.append_assoc, List.singleton_append]

theorem independent_chain_law (p : Params M Cv L) {C : Type}
    (out : List State → List State → C) (obs : C → ℚ) :
    ∀ n s bs xs,
      independentMean (QuerySampler.chain p out n s bs xs).toProgram
          (fun w => obs w.2) =
        Q22.chainE (fun moreBs moreXs =>
          obs (out (bs ++ moreBs) (xs ++ moreXs))) n := by
  intro n
  induction n with
  | zero =>
      intro s bs xs
      simp [QuerySampler.chain, Sampler.toProgram, independentMean, Q22.chainE]
  | succ n ih =>
      intro s bs xs
      simp only [QuerySampler.chain, Sampler.toProgram, independentMean, Q22.chainE]
      apply mean_congr
      intro b
      apply mean_congr
      intro x
      simpa only [List.append_assoc, List.singleton_append] using
        ih x (bs ++ [b]) (xs ++ [x])

#print axioms blaw_chainBS
#print axioms independent_chain_law

end AspisR1.QueryBackgroundLaw
end
