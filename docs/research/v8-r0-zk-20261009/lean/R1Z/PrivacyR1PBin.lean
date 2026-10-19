import R1Z.FinalR1PBin
import R1Z.LayoutTagR1PBin
import R1Z.LayoutCountR1PBin
import R1Z.SimulatorR1
import R1Z.Sem1UniformR1

-- Binary-format copy of `R1Z.PrivacyR1P` (LOG D76): the text is unchanged except that it is
-- built over `GamesR1PBin` / `LayoutR1P*Bin` (binary node index and `0x12 ‖ 2 children`).

/-! `privacy_R1_games'` (LOG D48.3, DESIGN-R1-REAL §6): the R1 privacy theorem
for the phase-indexed games `fsR1P` / `abR1P` against the explicit simulator
`simE`, with every `R1RealData` field discharged.  Its hypotheses are

* PackField, PublicBase, BuilderSoundOn;
* the D47 sampler premises `SemRows01 W`, `QM31SamplerLaw` (R-wire);
* R-rom: `RomModel W` (uniform table on a finite domain) and `RAddrIn`;
* R-causal: `RCausal`;
* R-commit: `RCommitBytes` (address grammar: leaves `0x10 ‖ tag ‖ value ‖
  salt`, nodes `0x12 ‖ 2 children` (binary, LOG D76), salts, seeds, bindings, expander blocks),
  the decoder's equal fibres (`hfib`), `RExh` (exhaustion = a 16-try
  little-endian word stream exhausted), the counter range `E ≤ 2^64` and the
  stream budgets `16 L ≤ 8 E`;
* R-wire: `eCm` (the Cm coin is the `RIdx` answers), `ROpen`, `RComLog`.

Error: `M q/2^255 + (M²/2^255 + εexh) + 0 + N·4096/(p⁴−1)` with
`M = N·|Pos1|`, `εexh = N·16(L₁+L₂)/2^496 + M/2^255`. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PrivacyR1PBin
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.HvzkV R0Z.HvzkS R0Z.RefPayload
  R1Z.Batched R1Z.PredicateR1 R1Z.MaskImageVR1 R1Z.PoleMassR1 R1Z.ModelsVR1 R1Z.SimulatorR1
  R1Z.GamesR1 R1Z.Sem1UniformR1 R1Z.GamesR1PBin R1Z.CouplingR1PBin R1Z.EventsR1PBin R1Z.FinalR1PBin
attribute [local instance] Classical.propDecidable

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-- Every field of `R1IdealModelS` for `fsR1P` and any simulator. -/
theorem idealModelS_R1P (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W)
    (N : ℕ) (hN : 0 < N) (P : Challenges K → Prop)
    (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop) (x : Statement K CommitHandle)
    (M Umin : ℕ) (sim : Challenges K → Tape K F → View K CommitHandle Aux R1Bat) :
    R1IdealModelS P (fsR1P W Pr N hN P Vp) (abR1P W N hN) x M Umin sim := by
  intro adv
  refine ⟨idCoupling _, fun _ => False, fun _ _ => [], ?_, ?_⟩
  · intro s _
    exact (retryOut_bit N (fun c => P (drawW W c)) (fun c t => sim (drawW W c) t)
      (fun c k v => (abR1 W N hN).extend adv x c k v) (fun c => (abR1 W N hN).fail adv x c)
      (fun o => bit (adv.decide o)) s).symm
  · intro j j' _ hp
    rcases hp with hp | hp <;> exact False.elim hp

/-- The R1 privacy theorem for the phase-indexed games. -/
theorem privacy_R1_games' (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W)
    (N : ℕ) (hN : 0 < N) (h : HonestProver K) (B : PackBasis F) (hB : R0Z.K4.PackField B)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (hpub : PublicBase F x.1)
    (hs : R0Z.HonestValidity.BuilderSoundOn h B x)
    (D : SemRows01 W) (L : QM31SamplerLaw D.s1)
    (R : RomModel W) (hin : ∀ w : h.Instance, RAddrIn W Pr R h B outputs x w)
    (hc : ∀ w : h.Instance, RCausal W Pr h B outputs x w)
    (hb : RCommitBytes W Pr) (cF : ℕ)
    (hfib : ∀ τ : Tape K F, (Finset.univ.filter
      (fun e : (Fin Pr.E₁ → OracleAnswer) × (Fin Pr.E₂ → OracleAnswer) =>
        Pr.tapeOf e.1 e.2 = some τ)).card = cF)
    (L₁ L₂ : ℕ) (hex : RExh Pr L₁ L₂) (hE₁ : Pr.E₁ ≤ 2 ^ 64) (hE₂ : Pr.E₂ ≤ 2 ^ 64)
    (h₁ : 16 * L₁ ≤ Pr.E₁ * 8) (h₂ : 16 * L₂ ≤ Pr.E₂ * 8)
    (eCm : W.Cm ≃ (RIdx → OracleAnswer)) (hop : ROpen Pr) (hcom : RComLog W Pr eCm h B outputs x) :
    ZK_FSS h B outputs (fsR1P W Pr N hN (P_R1 h.transport B hB) (fun h' => VR1 h')) x
      (simE h.transport B outputs x)
      (((N * n1 W Pr : ℕ) : ℚ) * (W.qmax : ℕ) / ((2 ^ 255 : ℕ) : ℚ) +
        (((N * n1 W Pr : ℕ) : ℚ) * ((N * n1 W Pr : ℕ) : ℚ) / ((2 ^ 255 : ℕ) : ℚ) +
          εexhP N L₁ L₂ (N * n1 W Pr)) +
        ((0 : ℕ) : ℚ) * ((0 : ℕ) : ℚ) / ((2 ^ 255 : ℕ) : ℚ) +
        (abR1P W N hN).N * ((4096 : ℚ) / (((2 ^ 31 - 1) ^ 4 - 1 : ℕ) : ℚ))) :=
  privacy_R1_eff h B hB outputs (fsR1P W Pr N hN (P_R1 h.transport B hB) (fun h' => VR1 h')) x
    hpub hs (abR1P W N hN) (N * n1 W Pr) 0 W.qmax (2 ^ 255) ((2 ^ 31 - 1) ^ 4 - 1)
    (εexhP N L₁ L₂ (N * n1 W Pr)) (by positivity)
    (realModel_R1P W Pr R eCm N hN (P_R1 h.transport B hB) (fun h' => VR1 h') h (VR1 h) B outputs x
      hin hc hb hop hcom (fun _ _ => Iff.rfl) cF hfib hE₁ hE₂ L₁ L₂ hex h₁ h₂)
    (idealModelS_R1P W Pr N hN _ _ x 0 (2 ^ 255) (simE h.transport B outputs x))
    (fun adv => sem1Uniform_abR1 W N hN D L adv x)

#print axioms idealModelS_R1P
#print axioms privacy_R1_games'
end R1Z.PrivacyR1PBin
