import R1Z.PremisesR1PBin

/-! Remaining causal and batch obligations, stated on the actual privacy
positions. No collision exclusion, successful-run restriction, or recovered
word is substituted for the universal RCausal condition. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PremisesR1PBin
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsAbortBounds R0Z.HvzkV
  R1Z.Batched R1Z.LensR1 R1Z.TranscriptR1 R1Z.GamesR1 R1Z.LazyFrozen
  R1Z.GamesR1PBin R1Z.CouplingR1PBin R1Z.LayoutR1PBin R1Z.EventsR1PBin

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-- Agreement on positions preceding `p` in the supplied prover order. -/
def Earlier (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W)
    (p : Pos1 Pr.E₁ Pr.E₂) (v v' : Pos1 Pr.E₁ Pr.E₂ → OracleAnswer) : Prop :=
  ∀ q, Pr.ord.symm q < Pr.ord.symm p → v q = v' q

/-- An exact position-indexed restatement of RCausal; no source assumption
is discharged by this change of index. -/
theorem causal_iff (W : R1Wire K CommitHandle Aux)
    (Pr : R1ProverP K CommitHandle Aux F W) (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : h.Instance) :
    RCausal W Pr h B outputs x w ↔
      ∀ sec d p v v', Earlier W Pr p v v' →
        attAddr W Pr h B outputs x w sec d v p =
          attAddr W Pr h B outputs x w sec d v' p := by
  constructor
  · intro H sec d p v v' he
    have hp := H sec d (Pr.ord.symm p) v v' (fun j hj =>
      he (Pr.ord j) (by simpa using hj))
    simpa using hp
  · intro H sec d i v v' he
    apply H sec d (Pr.ord i) v v'
    intro q hq
    have hq' : Pr.ord.symm q < i := by simpa using hq
    simpa using he (Pr.ord.symm q) hq'

/-- The root component of RCausal reduces to two strict predecessor facts
once its own AddressAt equation holds. Specialize T=1 for C2 and T=2 for folded. The
source's chronological cut alone does not supply these `Pr.ord` facts. -/
theorem root_causal_of_predecessors (W : R1Wire K CommitHandle Aux)
    (Pr : R1ProverP K CommitHandle Aux F W)
    (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : h.Instance) (T : Fin 3)
    (hr : AddressAt W Pr (.inl T))
    (prior : ∀ j : Fin 2,
      Pr.ord.symm (.inr (.inr (.inr (rootChild T j)))) <
        Pr.ord.symm (.inr (.inl T)))
    (sec : SecP) (d : OracleAnswer) (v v' : Pos1 Pr.E₁ Pr.E₂ → OracleAnswer)
    (he : Earlier W Pr (.inr (.inl T)) v v') :
    attAddr W Pr h B outputs x w sec d v (.inr (.inl T)) =
      attAddr W Pr h B outputs x w sec d v' (.inr (.inl T)) := by
  change Pr.caddr _ _ _ _ _ _ _ _ _ = Pr.caddr _ _ _ _ _ _ _ _ _
  rw [hr, hr]
  change nodeBytes (restOf v) (rootChild T) = nodeBytes (restOf v') (rootChild T)
  have hj (j : Fin 2) : restOf v (rootChild T j) = restOf v' (rootChild T j) :=
    he _ (prior j)
  simp only [nodeBytes, hj]

/-- Open-path membership distributes over the two transaction fibre sets. -/
theorem opened_union (a b : Fin 3 → Finset Fib) (c : Fin 3 ⊕ RIdx) :
    openedQ (fun T => a T ∪ b T) c ↔ openedQ a c ∨ openedQ b c := by
  rcases c with T | (i | i | ⟨T, u⟩ | ⟨T, u⟩ | ⟨T, n⟩)
  all_goals simp [openedQ, or_and_right, exists_or]

/-- Minimal batch facts suffice: the separate `covers` field is redundant.
The reads here must be normalized position lists, not raw repeated calls. -/
theorem open_of_batches (W : R1Wire K CommitHandle Aux)
    (Pr : R1ProverP K CommitHandle Aux F W)
    (fib : Challenges K → Fin 2 → Fin 3 → Finset Fib)
    (reads : Challenges K → Fin 2 → List (Fin 3 ⊕ RIdx))
    (cat : ∀ ch, Pr.openList ch = reads ch 0 ++ reads ch 1)
    (nodup : ∀ ch b, (reads ch b).Nodup)
    (cover : ∀ ch b c, c ∈ reads ch b ↔ openedQ (fib ch b) c)
    (union : ∀ ch T, Pr.openFib ch T = fib ch 0 T ∪ fib ch 1 T) : ROpen Pr := by
  refine ⟨?_, ⟨fib, reads, cat, nodup, cover, union⟩⟩
  intro ch c
  have hf : Pr.openFib ch = fun T => fib ch 0 T ∪ fib ch 1 T := funext (union ch)
  rw [cat, List.mem_append, cover, cover, hf, opened_union]

#print axioms causal_iff
#print axioms root_causal_of_predecessors
#print axioms opened_union
#print axioms open_of_batches
end R1Z.PremisesR1PBin
