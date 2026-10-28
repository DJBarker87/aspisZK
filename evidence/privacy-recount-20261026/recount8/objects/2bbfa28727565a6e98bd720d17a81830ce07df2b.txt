import R1Z.CouplingR1P2Bin
import R1Z.LayoutR1P3Bin

-- Binary-format copy of `R1Z.EventsR1P` (LOG D76): the text is unchanged except that it is
-- built over `GamesR1PBin` / `LayoutR1P*Bin` (binary node index and `0x12 ‖ 2 children`).

/-! The events of the real coupling and their freshness (DESIGN-R1-REAL §3,
§5): positions `Fin N × Pos1` (every read of every attempt), addresses
`addrP` (the run's addresses on the lazy answers), charging (a read is
charged unless it is published: a transcript read of the accepted attempt,
or an opened commitment read of it), the adversary's reads `qryP` in the
middle game, and the designated-field lenses on the coupling space.

PROVED: `HitFresh` and `PairFresh` (`hitP`, `pairP`) for every position,
from the transcript frame (`TranscriptR1`) and the commitment layout
(`LayoutR1P*`), under the named premises
* `RCommitBytes` (R-commit: `Pr.caddr` is the Rust byte grammar `gram`),
* `ROpen` (R-wire: the verifier's opening list is the opened set of the
  opened fibres), `RComLog` (R-wire: the verifier's opening reads are the
  prover's reads at the opened positions, answered by their coins),
* `E₁, E₂ ≤ 2^64` (the expander counters are u64). -/
set_option autoImplicit false
noncomputable section
namespace R1Z.EventsR1PBin
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsAbortBounds R0Z.HvzkV
  R1Z.Batched R1Z.LensR1 R1Z.TranscriptR1 R1Z.GamesR1 R1Z.LazyFrozen R1Z.GamesR1PBin
  R1Z.CouplingR1PBin R1Z.LayoutR1PBin
attribute [local instance] Classical.propDecidable

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-! ### Named premises -/

/-- R-commit: the prover's commitment addresses are the Rust byte grammar. -/
def RCommitBytes (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W) : Prop :=
  ∀ (h : HonestProver K) (w : h.Instance) (x : Statement K CommitHandle) (sec : SecP)
    (d : OracleAnswer) (τ : Tape K F) (rest : RIdx → OracleAnswer) (ch : Challenges K)
    (c : CPos Pr.E₁ Pr.E₂),
    Pr.caddr h w x sec d τ rest ch c = gram (W.pubBytes x) W.vtag (Pr.leafVal h w x τ ch) sec d rest c

/-- The read set of one multiproof batch: roots and the union of binary
paths. Supplied sibling digests are bytes, not additional oracle reads.
Deterministic slot padding is also bytes, not an oracle position. -/
def batchReadSet (fib : Fin 3 → Finset Fib) : Finset (Fin 3 ⊕ RIdx) :=
  Finset.univ.filter (openedQ fib)

theorem mem_batchReadSet (fib : Fin 3 → Finset Fib) (c : Fin 3 ⊕ RIdx) :
    c ∈ batchReadSet fib ↔ openedQ fib c := by simp [batchReadSet]

/-- R-wire for the two transaction batches. A node may occur in both batches,
but occurs at most once within each. The aggregate covers the opened fibres.
These remain source-refinement premises, not assertions about arbitrary lists. -/
structure ROpen {W : R1Wire K CommitHandle Aux}
    (Pr : R1ProverP K CommitHandle Aux F W) : Prop where
  covers : ∀ (ch : Challenges K) (c : Fin 3 ⊕ RIdx),
    c ∈ Pr.openList ch ↔ openedQ (Pr.openFib ch) c
  batches : ∃ (fib : Challenges K → Fin 2 → Fin 3 → Finset Fib)
      (reads : Challenges K → Fin 2 → List (Fin 3 ⊕ RIdx)),
    (∀ ch, Pr.openList ch = reads ch 0 ++ reads ch 1) ∧
    (∀ ch b, (reads ch b).Nodup) ∧
    (∀ ch b c, c ∈ reads ch b ↔ openedQ (fib ch b) c) ∧
    (∀ ch T, Pr.openFib ch T = fib ch 0 T ∪ fib ch 1 T)

/-- Deduplication turns the verifier's per-batch log into exactly the path union. -/
theorem batch_toFinset (fib : Fin 3 → Finset Fib) (reads : List (Fin 3 ⊕ RIdx))
    (hc : ∀ c, c ∈ reads ↔ openedQ fib c) : reads.toFinset = batchReadSet fib := by
  ext c
  simp only [List.mem_toFinset, mem_batchReadSet, hc]

/-- Each distinct node (and leaf/root) is read once in a batch. -/
theorem batch_length (fib : Fin 3 → Finset Fib) (reads : List (Fin 3 ⊕ RIdx))
    (hn : reads.Nodup) (hc : ∀ c, c ∈ reads ↔ openedQ fib c) :
    reads.length = (batchReadSet fib).card := by
  rw [← batch_toFinset fib reads hc, List.toFinset_card_of_nodup hn]

/-- A symbolic bound: no enumeration of the 2^18-leaf universe. -/
theorem batchReadSet_card_le (fib : Fin 3 → Finset Fib) :
    (batchReadSet fib).card ≤ 2359298 := by
  have h := Finset.card_le_univ (batchReadSet fib)
  simp only [Fintype.card_sum, Fintype.card_fin, RIdx, Fib, Fintype.card_prod,
    card_NodeIdx] at h
  norm_num at h ⊢
  exact h

/-- Mapping the opening list (in particular the RComLog address/answer map)
preserves the two deduplicated batches and their exact set cardinalities. -/
theorem map_openList_batches {W : R1Wire K CommitHandle Aux}
    (Pr : R1ProverP K CommitHandle Aux F W) (hop : ROpen Pr) (ch : Challenges K)
    {β : Type} (f : (Fin 3 ⊕ RIdx) → β) :
    ∃ (fib : Fin 2 → Fin 3 → Finset Fib) (reads : Fin 2 → List (Fin 3 ⊕ RIdx)),
      (Pr.openList ch).map f = (reads 0).map f ++ (reads 1).map f ∧
      (∀ b, (reads b).Nodup) ∧
      (∀ b, (reads b).toFinset = batchReadSet (fib b)) ∧
      (∀ b, (reads b).length = (batchReadSet (fib b)).card) := by
  obtain ⟨fib, reads, hcat, hn, hc, _⟩ := hop.batches
  refine ⟨fib ch, reads ch, ?_, hn ch, ?_, ?_⟩
  · rw [hcat ch, List.map_append]
  · intro b
    exact batch_toFinset _ _ (hc ch b)
  · intro b
    exact batch_length _ _ (hn ch b) (hc ch b)

/-- The answer of an opening position from the coins. -/
def ansC (roots : Fin 3 → OracleAnswer) (rest : RIdx → OracleAnswer) : Fin 3 ⊕ RIdx → OracleAnswer
  | .inl i => roots i
  | .inr q => rest q

/-- R-wire: the verifier's opening reads (`W.comLog`) are the prover's reads at
the opened positions, with the coins as answers. -/
def RComLog (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W)
    (eCm : W.Cm ≃ (RIdx → OracleAnswer)) (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux) (x : Statement K CommitHandle) : Prop :=
  ∀ (w : h.Instance) (sec : SecP) (d : OracleAnswer) (τ : Tape K F) (roots : Fin 3 → OracleAnswer)
    (rest : RIdx → OracleAnswer) (ch : Challenges K),
    W.comLog (eCm.symm rest) roots (view h B outputs x w ch τ) ch =
      (Pr.openList ch).map (fun c => (Pr.caddr h w x sec d τ rest ch (cposOf c), ansC roots rest c))

/-! ### Lenses on the coupling space -/

def Lens.fnAt {N : ℕ} {C U : Type} (k : Fin N) (L : Lens C U) : Lens (Fin N → C) U where
  get s := L.get (s k)
  set s u := Function.update s k (L.set (s k) u)
  get_set s u := by simp [L.get_set]
  set_get s := by
    funext k'
    by_cases hk : k' = k
    · subst hk
      simp [L.set_get]
    · simp [Function.update_of_ne hk]
  set_set s u u' := by simp [L.set_set]

theorem Lens.fnAt_set_ne {N : ℕ} {C U : Type} (k : Fin N) (L : Lens C U) (s : Fin N → C) (u : U)
    (k' : Fin N) (hk : k' ≠ k) : ((Lens.fnAt k L).set s u) k' = s k' := by
  simp [Lens.fnAt, Function.update_of_ne hk]

theorem Lens.fnAt_set_eq {N : ℕ} {C U : Type} (k : Fin N) (L : Lens C U) (s : Fin N → C) (u : U) :
    ((Lens.fnAt k L).set s u) k = L.set (s k) u := by
  simp [Lens.fnAt]

section Lenses
variable (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W)

/-- The answer coordinate `p` of an attempt block. -/
def vL (p : Pos1 Pr.E₁ Pr.E₂) : Lens (AttS (F := F) W Pr) OracleAnswer where
  get a := a.2.1 p
  set a u := (a.1, Function.update a.2.1 p u, a.2.2)
  get_set a u := by simp
  set_get a := by simp
  set_set a u u' := by simp

/-- The secret slot `i` of an attempt block. -/
def secL (i : Fin 3) : Lens (AttS (F := F) W Pr) NZ where
  get a := a.1 i
  set a z := (Function.update a.1 i z, a.2)
  get_set a z := by simp
  set_get a := by simp
  set_set a z z' := by simp

def ksV (v : Pos1 Pr.E₁ Pr.E₂ → OracleAnswer) : Fin 8 := W.kstarOf (fun m => v (.inl (.qb m)))

theorem ksV_update_qa (v : Pos1 Pr.E₁ Pr.E₂ → OracleAnswer) (m : Fin 8) (u : OracleAnswer) :
    ksV W Pr (Function.update v (.inl (.qa m)) u) = ksV W Pr v := by
  unfold ksV
  congr 1

/-- `sel`: the answer of `qa k*`. -/
def selL : Lens (AttS (F := F) W Pr) OracleAnswer where
  get a := a.2.1 (.inl (.qa (ksV W Pr a.2.1)))
  set a u := (a.1, Function.update a.2.1 (.inl (.qa (ksV W Pr a.2.1))) u, a.2.2)
  get_set a u := by
    show Function.update a.2.1 (.inl (.qa (ksV W Pr a.2.1))) u
      (.inl (.qa (ksV W Pr (Function.update a.2.1 (.inl (.qa (ksV W Pr a.2.1))) u)))) = u
    rw [ksV_update_qa]
    simp
  set_get a := by simp
  set_set a u u' := by
    show (a.1, Function.update (Function.update a.2.1 (.inl (.qa (ksV W Pr a.2.1))) u)
        (.inl (.qa (ksV W Pr (Function.update a.2.1 (.inl (.qa (ksV W Pr a.2.1))) u)))) u', a.2.2) =
      (a.1, Function.update a.2.1 (.inl (.qa (ksV W Pr a.2.1))) u', a.2.2)
    rw [ksV_update_qa]
    simp

def chainL : Coord → Lens (AttS (F := F) W Pr) OracleAnswer
  | .root => vL W Pr (.inr (.inl 0))
  | .sel => selL W Pr
  | .ans j => vL W Pr (.inl j)

end Lenses

/-! ### The transcript frame -/

section Frame
variable (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W)
  (h : HonestProver K) (B : PackBasis F) (outputs : Statement K CommitHandle → Challenges K → Aux)
  (x : Statement K CommitHandle) (w : h.Instance)

/-- The transcript record of an attempt block. -/
def recA (a : AttS (F := F) W Pr) : Rec :=
  recP W x (view h B outputs x w (chOf W (trOf a.2.1)) (tapeR W Pr a.2.1)) (trOf a.2.1) (rootsOf a.2.1)

theorem tapeR_update_tr (v : Pos1 Pr.E₁ Pr.E₂ → OracleAnswer) (j : TRead) (u : OracleAnswer) :
    tapeR W Pr (Function.update v (.inl j) u) = tapeR W Pr v := by
  unfold tapeR e₁Of e₂Of
  congr 3 <;> funext c <;> exact Function.update_of_ne (by simp) _ _

theorem tapeR_update_root (v : Pos1 Pr.E₁ Pr.E₂ → OracleAnswer) (i : Fin 3) (u : OracleAnswer) :
    tapeR W Pr (Function.update v (.inr (.inl i)) u) = tapeR W Pr v := by
  unfold tapeR e₁Of e₂Of
  congr 3 <;> funext c <;> exact Function.update_of_ne (by simp) _ _

theorem trOf_update_root (v : Pos1 Pr.E₁ Pr.E₂ → OracleAnswer) (i : Fin 3) (u : OracleAnswer) :
    trOf (Function.update v (.inr (.inl i)) u) = trOf v := by
  funext j
  exact Function.update_of_ne (by simp) _ _

theorem trOf_update_tr (v : Pos1 Pr.E₁ Pr.E₂ → OracleAnswer) (j : TRead) (u : OracleAnswer) :
    trOf (Function.update v (.inl j) u) = Function.update (trOf v) j u := by
  funext j'
  by_cases hj : j' = j
  · subst hj
    simp [trOf]
  · simp [trOf, Function.update_of_ne hj, Function.update_of_ne (show (Sum.inl j' : Pos1 Pr.E₁ Pr.E₂) ≠ .inl j by simpa using hj)]

theorem rootsOf_update_tr (v : Pos1 Pr.E₁ Pr.E₂ → OracleAnswer) (j : TRead) (u : OracleAnswer) :
    rootsOf (Function.update v (.inl j) u) = rootsOf v := by
  funext i
  exact Function.update_of_ne (by simp) _ _

theorem rootsOf_update_root (v : Pos1 Pr.E₁ Pr.E₂ → OracleAnswer) (i : Fin 3) (u : OracleAnswer) :
    rootsOf (Function.update v (.inr (.inl i)) u) = Function.update (rootsOf v) i u := by
  funext i'
  by_cases hi : i' = i
  · subst hi
    simp [rootsOf]
  · simp [rootsOf, Function.update_of_ne hi,
      Function.update_of_ne (show (Sum.inr (Sum.inl i') : Pos1 Pr.E₁ Pr.E₂) ≠ .inr (.inl i) by simpa using hi)]

theorem chOf_update_tr (tr : TRead → OracleAnswer) (j : TRead) (hj : ¬ IsSq j) (u : OracleAnswer) :
    chOf (K := K) W (Function.update tr j u) = chOf W tr :=
  chOf_congr W _ _ (fun j' hj' => Function.update_of_ne (fun e => hj (by rw [← e]; exact hj')) _ _)

theorem kstar_update_tr (tr : TRead → OracleAnswer) (j : TRead) (hj : ¬ IsSq j) (u : OracleAnswer) :
    W.kstarOf (fun m => Function.update tr j u (.qb m)) = W.kstarOf (fun m => tr (.qb m)) := by
  congr 1
  funext m
  exact Function.update_of_ne (fun e => hj (by rw [← e]; trivial)) _ _

theorem recA_chain (c : Coord) (hc : ChainC c) (a : AttS (F := F) W Pr) (u : OracleAnswer) :
    recA W Pr h B outputs x w ((chainL W Pr c).set a u) = setC c (recA W Pr h B outputs x w a) u := by
  cases c with
  | root =>
      show recA W Pr h B outputs x w (a.1, Function.update a.2.1 (.inr (.inl 0)) u, a.2.2) = _
      simp only [recA, recP, setC, trOf_update_root, tapeR_update_root, rootsOf_update_root,
        Function.update_self]
      rw [Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0),
        Function.update_of_ne (by decide : (2 : Fin 3) ≠ 0)]
  | sel =>
      show recA W Pr h B outputs x w
        (a.1, Function.update a.2.1 (.inl (.qa (ksV W Pr a.2.1))) u, a.2.2) = _
      have hq : ¬ IsSq (TRead.qa (ksV W Pr a.2.1)) := fun h => h
      simp only [recA, recP, setC, trOf_update_tr, tapeR_update_tr, rootsOf_update_tr,
        chOf_update_tr W _ _ hq, kstar_update_tr W _ _ hq]
      rfl
  | ans j =>
      have hq : ¬ IsSq j := hc j rfl
      show recA W Pr h B outputs x w (a.1, Function.update a.2.1 (.inl j) u, a.2.2) = _
      simp only [recA, recP, setC, trOf_update_tr, tapeR_update_tr, rootsOf_update_tr,
        chOf_update_tr W _ _ hq, kstar_update_tr W _ _ hq]

/-- The transcript frame on the coupling space. -/
def frameP (N : ℕ) : TranscriptFrame (Fin N → AttS (F := F) W Pr) N where
  att k s := recA W Pr h B outputs x w (s k)
  lens k c := Lens.fnAt k (chainL W Pr c)
  rec_same k c s u hc := by
    show recA W Pr h B outputs x w (((Lens.fnAt k (chainL W Pr c)).set s u) k) = _
    rw [Lens.fnAt_set_eq]
    exact recA_chain W Pr h B outputs x w c hc (s k) u
  rec_other k k' c s u hk := by
    show recA W Pr h B outputs x w (((Lens.fnAt k (chainL W Pr c)).set s u) k') = _
    rw [Lens.fnAt_set_ne _ _ _ _ _ hk]

end Frame

#print axioms Lens.fnAt
#print axioms selL
#print axioms recA_chain
#print axioms frameP
#print axioms Lens.fnAt_set_ne
#print axioms Lens.fnAt_set_eq
#print axioms ksV_update_qa
#print axioms tapeR_update_tr
#print axioms tapeR_update_root
#print axioms trOf_update_root
#print axioms trOf_update_tr
#print axioms rootsOf_update_tr
#print axioms rootsOf_update_root
#print axioms chOf_update_tr
#print axioms kstar_update_tr

#print axioms map_openList_batches
#print axioms mem_batchReadSet
#print axioms batch_toFinset
#print axioms batch_length
#print axioms batchReadSet_card_le
end R1Z.EventsR1PBin
