import R1Z.EventsR1PBin
import R1Z.WireBindingLengthsR1PBin

/-! Exact privacy-interface reductions. These do not import, copy, or assert
soundness-tree source refinements. In particular a recovered word at a
collision-free cut is not causality on arbitrary answer vectors. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PremisesR1PBin
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsAbortBounds R0Z.HvzkV
  R1Z.Batched R1Z.LensR1 R1Z.TranscriptR1 R1Z.GamesR1 R1Z.LazyFrozen
  R1Z.GamesR1PBin R1Z.CouplingR1PBin R1Z.LayoutR1PBin R1Z.EventsR1PBin

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-- One constructor-specific source address equation, with exactly the
quantifiers in `RCommitBytes`. The leaf bytes remain `Pr.leafVal`. -/
def AddressAt (W : R1Wire K CommitHandle Aux)
    (Pr : R1ProverP K CommitHandle Aux F W) (c : CPos Pr.E₁ Pr.E₂) : Prop :=
  ∀ (h : HonestProver K) (w : h.Instance) (x : Statement K CommitHandle)
    (sec : SecP) (d : OracleAnswer) (τ : Tape K F) (rest : RIdx → OracleAnswer)
    (ch : Challenges K),
    Pr.caddr h w x sec d τ rest ch c =
      gram (W.pubBytes x) W.vtag (Pr.leafVal h w x τ ch) sec d rest c

/-- Eight independently checkable source families: roots, mask/source
expansion, binding, seed, salt, leaf, and internal binary nodes. -/
theorem commit_bytes_iff (W : R1Wire K CommitHandle Aux)
    (Pr : R1ProverP K CommitHandle Aux F W) :
    RCommitBytes W Pr ↔
      (∀ T, AddressAt W Pr (.inl T)) ∧
      (∀ c, AddressAt W Pr (.inr (.inl (.inl c)))) ∧
      (∀ c, AddressAt W Pr (.inr (.inl (.inr c)))) ∧
      (∀ b, AddressAt W Pr (.inr (.inr (qBind b)))) ∧
      (∀ i, AddressAt W Pr (.inr (.inr (qSeed i)))) ∧
      (∀ T u, AddressAt W Pr (.inr (.inr (qSalt T u)))) ∧
      (∀ T u, AddressAt W Pr (.inr (.inr (qLeaf T u)))) ∧
      (∀ T n, AddressAt W Pr (.inr (.inr (qNode T n)))) := by
  constructor
  · intro H
    have H' : ∀ c, AddressAt W Pr c := fun c h w x sec d τ rest ch =>
      H h w x sec d τ rest ch c
    exact ⟨fun _ => H' _, fun _ => H' _, fun _ => H' _, fun _ => H' _,
      fun _ => H' _, fun _ _ => H' _, fun _ _ => H' _, fun _ _ => H' _⟩
  · rintro ⟨hr, he₁, he₂, hb, hs, hsa, hl, hn⟩ h w x sec d τ rest ch c
    have H' : AddressAt W Pr c := by
      rcases c with T | (e | e) | (b | i | ⟨T, u⟩ | ⟨T, u⟩ | ⟨T, n⟩)
      · exact hr T
      · exact he₁ e
      · exact he₂ e
      · exact hb b
      · exact hs i
      · exact hsa T u
      · exact hl T u
      · exact hn T n
    exact H' h w x sec d τ rest ch

/-- Once the commitment grammar is supplied, the remaining RComLog fact is
an ordered equality of complete byte/answer lists, with exactly the original
universal quantifiers. Set equality is insufficient. -/
theorem com_log_iff (W : R1Wire K CommitHandle Aux)
    (Pr : R1ProverP K CommitHandle Aux F W) (hc : RCommitBytes W Pr)
    (eCm : W.Cm ≃ (RIdx → OracleAnswer)) (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) :
    RComLog W Pr eCm h B outputs x ↔
      ∀ (w : h.Instance) (sec : SecP) (d : OracleAnswer) (τ : Tape K F)
        (roots : Fin 3 → OracleAnswer) (rest : RIdx → OracleAnswer) (ch : Challenges K),
      W.comLog (eCm.symm rest) roots (view h B outputs x w ch τ) ch =
        (Pr.openList ch).map (fun c =>
          (gram (W.pubBytes x) W.vtag (Pr.leafVal h w x τ ch) sec d rest (cposOf (E₁ := Pr.E₁) (E₂ := Pr.E₂) c),
            ansC roots rest c)) := by
  constructor
  · intro H w sec d τ roots rest ch
    simpa only [hc h w x sec d τ rest ch] using H w sec d τ roots rest ch
  · intro H w sec d τ roots rest ch
    simpa only [hc h w x sec d τ rest ch] using H w sec d τ roots rest ch

/-- The inverse law required of the coordinate equivalence. This is not a
construction of an equivalence for the arbitrary finite carrier `W.Cm`. -/
theorem cm_coordinate (W : R1Wire K CommitHandle Aux)
    (eCm : W.Cm ≃ (RIdx → OracleAnswer)) (rest : RIdx → OracleAnswer) (q : RIdx) :
    eCm (eCm.symm rest) q = rest q := by rw [eCm.apply_symm_apply]

/-- A root address depends on exactly its two child answers once its grammar
is supplied. Applies to C1, C2, and folded roots, even on inconsistent vectors. -/
theorem root_address_congr (W : R1Wire K CommitHandle Aux)
    (Pr : R1ProverP K CommitHandle Aux F W) (hc : RCommitBytes W Pr)
    (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : h.Instance) (sec : SecP) (d : OracleAnswer)
    (v v' : Pos1 Pr.E₁ Pr.E₂ → OracleAnswer) (T : Fin 3)
    (he : ∀ j : Fin 2, restOf v (rootChild T j) = restOf v' (rootChild T j)) :
    attAddr W Pr h B outputs x w sec d v (.inr (.inl T)) =
      attAddr W Pr h B outputs x w sec d v' (.inr (.inl T)) := by
  change Pr.caddr _ _ _ _ _ _ _ _ _ = Pr.caddr _ _ _ _ _ _ _ _ _
  rw [hc, hc]
  change nodeBytes (restOf v) (rootChild T) = nodeBytes (restOf v') (rootChild T)
  simp only [nodeBytes, he]

/-- Two distinct query indices can select the same folded leaf. The raw
pre-dedup leaf-call position list is then not the Nodup batch of ROpen. -/
theorem repeated_folded_leaf_not_nodup :
    ¬ ([Sum.inr (qLeaf 2 ⟨0 / 4, by decide⟩),
        Sum.inr (qLeaf 2 ⟨1 / 4, by decide⟩)] : List (Fin 3 ⊕ RIdx)).Nodup := by
  simp

/-- D79, including all three addendum classes, supplies separation only after
the caller supplies membership in the concrete extended wire carrier. -/
theorem classified_separation (w : WireLengthsR1PBin.Wire)
    (answers : RIdx → OracleAnswer) (children : Fin 2 → RIdx)
    (bs : List UInt8)
    (member : ∃ read : WireBindingLengthsR1PBin.ExtendedRead, bs = read.bytes w) :
    nodeBytes answers children ≠ bs := by
  obtain ⟨read, rfl⟩ := member
  exact WireBindingLengthsR1PBin.node_ne_extended_read w answers children read

#print axioms commit_bytes_iff
#print axioms com_log_iff
#print axioms cm_coordinate
#print axioms root_address_congr
#print axioms repeated_folded_leaf_not_nodup
#print axioms classified_separation
end R1Z.PremisesR1PBin
