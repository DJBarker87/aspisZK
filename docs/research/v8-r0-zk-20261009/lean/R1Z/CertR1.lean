import R1Z.PredicateR1
import R1Z.CertSound

/-! D38.5 (zf1/DESIGN-P-CERT.txt §2.3, §5.2): the generic checker semantics of
`R1Z.CertSound` instantiated at the exact types of the `P_R1` conjuncts.

Each theorem takes
* the certificate data (kernel entries, combination matrices, `U`, pivot and
  free lists, right inverses) and the Prop the Boolean checker decides
  (`PreOK`, `PreOK₂`, `EchOK`, `RinvOK`, a field product, a list length);
* the row-formula correspondence as named hypotheses `rf_*` (the D34.3 items
  and their siblings, DESIGN-P-CERT §2.3 (C2)); none is asserted here.

`p_r1_of_cert` assembles them into `P_R1`.  No concrete row, query or
challenge is evaluated. -/

set_option autoImplicit false

noncomputable section

namespace R1Z.CertR1

open scoped BigOperators
open R0P R0Z.MaskLayout R0Z.HonestView R0Z.Partition R0Z.D12 R0Z.K4
open R1Z.Batched R1Z.VerifierRelationsR1 R1Z.PredicateR1 R1Z.CertSound

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-- HalfOK from a supplied inverse. -/
theorem halfOK_of_cert (ch : Challenges K) (y : K) (hy : (alpha ch 9 - 1 / 2) * y = 1) :
    HalfOK ch :=
  half_sound _ _ y hy

/-- QueryCard from the decoded list (RF-dec: the decoder's query set is the
list's `toFinset`). -/
theorem queryCard_of_cert (ch : Challenges K) (l : List (Fin 262144))
    (rf_dec : ch.queries = l.toFinset) (hl : l.length ≤ 22) : QueryCard ch := by
  unfold QueryCard
  rw [rf_dec]
  exact card_sound l hl

/-- QPrime_R1 from a two-level preimage certificate on the stacked mask-lane
sources. -/
theorem qprime_of_cert (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (hB : PackField B)
    (ch : Challenges K) {a N m n : ℕ} (src : Fin N → M K F)
    (Own : Fin a → Fin N → F) (Rnd : Fin 1084 → Fin N → F)
    (ιo : (Fin a → F) →ₗ[F] Payload K R1Bat)
    (ιr : (Fin 1084 → F) →ₗ[F] R0Z.PayloadSplit.RoundPayload K)
    (rf_own : ∀ t, R0Z.SilentReduction.ownMap (Bat := R1Bat) π B ch (src t) = ιo (col Own t))
    (rf_round : ∀ t, R0Z.Z4Maps.roundMaskMap (Bat := R1Bat) π B ch (src t) = ιr (col Rnd t))
    (T : Fin n → Fin 1084 → F)
    (rf_chain : R0Z.SilentReduction.ChainT0K4 (Bat := R1Bat) B hB ch ≤
      Submodule.span F (Set.range fun i => ιr (T i)))
    (ents : Fin m → KerEntry N F) (Y : Fin n → Fin m → F)
    (h : PreOK Own Rnd ents Y T) : QPrime_R1 π B hB ch := by
  have hs := span_sound ⊤ (R0Z.SilentReduction.ownMap (Bat := R1Bat) π B ch)
    (R0Z.Z4Maps.roundMaskMap (Bat := R1Bat) π B ch) ιo ιr src (fun _ => Submodule.mem_top)
    Own Rnd rf_own rf_round ents Y T _ rf_chain h
  rw [top_inf_eq] at hs
  exact hs

/-- BCondG_R1 from the echelon certificate of `relR1`'s limb functionals and
preimages of the kernel generators in `V_G`. -/
theorem bcondG_of_cert (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    {a₁ a₂ nb NG mG q r k : ℕ} (srcG : Fin NG → M K F)
    (rf_src : ∀ t, srcG t ∈ Gonly (K := K) (F := F))
    (Z₁ : Fin a₁ → Fin NG → F) (Z₂ : Fin a₂ → Fin NG → F) (Bt : Fin nb → Fin NG → F)
    (ιo : (Fin a₁ → F) →ₗ[F] Payload K R1Bat)
    (ιr : (Fin a₂ → F) →ₗ[F] R0Z.PayloadSplit.RoundPayload K)
    (ιb : (Fin nb → F) →ₗ[F] (R1Bat → K))
    (rf_own : ∀ t, R0Z.SilentReduction.ownMap (Bat := R1Bat) π B ch (srcG t) = ιo (col Z₁ t))
    (rf_round : ∀ t, R0Z.Z4Maps.roundMaskMap (Bat := R1Bat) π B ch (srcG t) = ιr (col Z₂ t))
    (rf_bat : ∀ t, R0Z.SilentReduction.batMap (Bat := R1Bat) π B ch (srcG t) = ιb (col Bt t))
    (Rel : Fin q → Fin nb → F)
    (rf_rel : ∀ x ∈ B0R1' (F := F) π ch,
      ∃ v : Fin nb → F, (∀ y, ∑ c, Rel y c * v c = 0) ∧ ιb v = x)
    (U : Fin r → Fin q → F) (piv : Fin r → Fin nb) (fr : Fin k → Fin nb)
    (hE : EchOK (Emat U Rel) piv fr)
    (ents : Fin mG → KerEntry NG F) (YG : Fin k → Fin mG → F)
    (h : PreOK₂ Z₁ Z₂ Bt ents YG (fun f => nvec (Emat U Rel) piv fr f)) :
    BCondG_R1 π B ch :=
  bcond_sound U Rel piv fr ιb (B0R1' (F := F) π ch) (V_G π B ch) rf_rel hE fun f =>
    pre_sound₂ (Gonly (K := K) (F := F)) (R0Z.SilentReduction.ownMap (Bat := R1Bat) π B ch)
      (R0Z.Z4Maps.roundMaskMap (Bat := R1Bat) π B ch)
      (R0Z.SilentReduction.batMap (Bat := R1Bat) π B ch) ιo ιr ιb srcG rf_src Z₁ Z₂ Bt
      rf_own rf_round rf_bat ents YG _ h f

/-- C1Lift_c from a right inverse of the selected eligible-noise columns. -/
theorem c1lift_of_cert (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    (c : Fin 16) {w : ℕ} (src : Fin w → (Fin 1024 → K))
    (rf_src : ∀ t, src t ∈ Vsem (K := K) (F := F) (Fin.castLE (by omega) c))
    (ι : (Fin w → F) →ₗ[F] (OwnCell → K))
    (rf_obs : (Wsem (K := K) (F := F)).map
      (obs (Bat := R1Bat) π B ch (Fin.castLE (by omega) c)) ≤ LinearMap.range ι)
    (O : Fin w → Fin w → F)
    (rf_col : ∀ t, obs (Bat := R1Bat) π B ch (Fin.castLE (by omega) c) (src t) = ι (col O t))
    (U : Fin w → Fin w → F) (h : RinvOK O U) : C1Lift (Bat := R1Bat) π B ch c :=
  lift_sound _ _ _ ι rf_obs src rf_src O rf_col U h

/-- H1Lift from a right inverse of the selected H1-padding columns. -/
theorem h1lift_of_cert (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (hB : PackField B)
    (ch : Challenges K) {w : ℕ} (src : Fin w → (Fin 1024 → K))
    (rf_src : ∀ t, src t ∈ Ph1 B)
    (ι : (Fin w → F) →ₗ[F] (OwnCell → K))
    (rf_obs : (Wh1 B hB).map (obs (Bat := R1Bat) π B ch 26) ≤ LinearMap.range ι)
    (O : Fin w → Fin w → F) (rf_col : ∀ t, obs (Bat := R1Bat) π B ch 26 (src t) = ι (col O t))
    (U : Fin w → Fin w → F) (h : RinvOK O U) : H1Lift (Bat := R1Bat) π B hB ch :=
  lift_sound _ _ _ ι rf_obs src rf_src O rf_col U h

/-- Assembly: the seven conjuncts of `P_R1`.  `rf_sem` is the decoder premise
for SemK4 (DESIGN-P-CERT §1.2: on R1 the semantic rows are QM31 samples). -/
theorem p_r1_of_cert (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (hB : PackField B)
    (ch : Challenges K)
    (hHalf : HalfOK ch) (rf_sem : SemK4 B hB ch) (hQ : QPrime_R1 π B hB ch)
    (hG : BCondG_R1 π B ch) (hC1 : ∀ c : Fin 16, C1Lift (Bat := R1Bat) π B ch c)
    (hH1 : H1Lift (Bat := R1Bat) π B hB ch) (hCard : QueryCard ch) : P_R1 π B hB ch :=
  ⟨hHalf, rf_sem, hQ, hG, hC1, hH1, hCard⟩

#print axioms halfOK_of_cert
#print axioms queryCard_of_cert
#print axioms qprime_of_cert
#print axioms bcondG_of_cert
#print axioms c1lift_of_cert
#print axioms h1lift_of_cert
#print axioms p_r1_of_cert

end R1Z.CertR1

end
