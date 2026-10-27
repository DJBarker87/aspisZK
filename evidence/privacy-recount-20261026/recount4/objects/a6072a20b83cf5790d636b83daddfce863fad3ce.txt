import R1Z.SimulatorSupportBin
import R1Z.EventsR1PBin

/-! ZF2's verifier programming uses the binary multiproof read sets. The
payload simulator has no tree geometry: it is `simE` of RefPayload. Geometry
enters through W.comLog and progOracle. RComLog is stated on honest views;
finite-law support transports it to simE on precisely P_R1 ∧ VR1, the domain
of hvzk_R1S. No additional simulator-wire premise is introduced. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.SimulatorLogR1PBin
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.RefPayload
  R1Z.Batched R1Z.MaskImageVR1 R1Z.PredicateR1 R1Z.PoleMassR1 R1Z.SimulatorR1
  R1Z.GamesR1 R1Z.GamesR1PBin R1Z.EventsR1PBin R1Z.LayoutR1PBin
attribute [local instance] Classical.propDecidable

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-- On the HVZK domain, every simulated payload has an honest-view preimage.
The witness/tape are used only in this proof, never by simE. -/
theorem simE_honest_preimage (h : HonestProver K) (B : PackBasis F)
    (hB : R0Z.K4.PackField B)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (hpub : PublicBase F x.1)
    (hs : R0Z.HonestValidity.BuilderSoundOn h B x)
    (w : h.Instance) (ch : Challenges K) (hP : P_R1 h.transport B hB ch)
    (hV : VR1 h ch w) (hw : h.public w = x.1) (t : Tape K F) :
    ∃ τ, view (Bat := R1Bat) h B outputs x w ch τ = simE h.transport B outputs x ch t :=
  SimulatorSupportBin.equalLaws_output _ _
    (hvzk_R1S h B hB outputs x hpub hs w ch hP hV hw) t

/-- The actual comLog at a simulated view is the concatenation of two
binary batches. Each batch reads exactly batchReadSet, without duplicates;
supplied siblings and slot padding add no read positions. -/
theorem simE_comLog_batches (W : R1Wire K CommitHandle Aux)
    (Pr : R1ProverP K CommitHandle Aux F W)
    (h : HonestProver K) (B : PackBasis F) (hB : R0Z.K4.PackField B)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (hpub : PublicBase F x.1)
    (hs : R0Z.HonestValidity.BuilderSoundOn h B x)
    (eCm : W.Cm ≃ (RIdx → OracleAnswer)) (hb : RCommitBytes W Pr) (hop : ROpen Pr)
    (hcom : RComLog W Pr eCm h B outputs x)
    (w : h.Instance) (ch : Challenges K) (hP : P_R1 h.transport B hB ch)
    (hV : VR1 h ch w) (hw : h.public w = x.1) (t : Tape K F)
    (sec : SecP) (d : OracleAnswer) (roots : Fin 3 → OracleAnswer)
    (rest : RIdx → OracleAnswer) :
    ∃ (τ : Tape K F) (fib : Fin 2 → Fin 3 → Finset Fib)
      (reads : Fin 2 → List (Fin 3 ⊕ RIdx)),
      W.comLog (eCm.symm rest) roots (simE h.transport B outputs x ch t) ch =
        (reads 0).map (fun c =>
          (gram (E₁ := Pr.E₁) (E₂ := Pr.E₂) (W.pubBytes x) W.vtag (Pr.leafVal h w x τ ch) sec d rest (cposOf c),
            ansC roots rest c)) ++
        (reads 1).map (fun c =>
          (gram (E₁ := Pr.E₁) (E₂ := Pr.E₂) (W.pubBytes x) W.vtag (Pr.leafVal h w x τ ch) sec d rest (cposOf c),
            ansC roots rest c)) ∧
      (∀ b, (reads b).Nodup) ∧
      (∀ b, (reads b).toFinset = batchReadSet (fib b)) ∧
      (∀ b, (reads b).length = (batchReadSet (fib b)).card) ∧
      (∀ T, Pr.openFib ch T = fib 0 T ∪ fib 1 T) := by
  obtain ⟨τ, hτ⟩ := simE_honest_preimage h B hB outputs x hpub hs w ch hP hV hw t
  obtain ⟨fib, reads, hcat, hn, hc, hu⟩ := hop.batches
  refine ⟨τ, fib ch, reads ch, ?_, hn ch, ?_, ?_, hu ch⟩
  · rw [← hτ, hcom w sec d τ roots rest ch]
    simp_rw [hb h w x sec d τ rest ch]
    rw [hcat ch, List.map_append]
  · intro b
    exact batch_toFinset _ _ (hc ch b)
  · intro b
    exact batch_length _ _ (hn ch b) (hc ch b)

/-- The ideal game's programmed table is exactly its verifier log: transcript
reads followed by comLog at the explicit simulated view, with fallback only
when the address is absent. Duplicate reads across batches use List.lookup. -/
theorem simE_progOracle (W : R1Wire K CommitHandle Aux)
    (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (ch : Challenges K) (t : Tape K F)
    (c : R1Coins W.Cm W.Tab) (tab : W.Tab) (a : List UInt8) :
    progOracle W x (simE h.transport B outputs x ch t) c tab a =
      match List.lookup a
        (tLog W x (simE h.transport B outputs x ch t) c ++
          W.comLog c.2.2.1 c.2.1 (simE h.transport B outputs x ch t) (drawW W c)) with
      | some v => v
      | none => W.look tab a := rfl

#print axioms simE_honest_preimage
#print axioms simE_comLog_batches
#print axioms simE_progOracle
end R1Z.SimulatorLogR1PBin
