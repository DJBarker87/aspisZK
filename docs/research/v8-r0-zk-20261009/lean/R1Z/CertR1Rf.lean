import R1Z.CertR1
import R1Z.RfDec
import R1Z.RfSrc
import R1Z.RfChain

/-! D49.4 C2: `CertR1` with the proved row-formula premises discharged.

Discharged here (proved in `R1Z.RfDec`, `R1Z.RfSrc`, `R1Z.RfChain`):
* RF-dec: the challenge record is `RfDec.decode B w raw`; `rf_dec` (queries) is
  `rfl`, α₉ is decoded row 24, and `SemK4` follows from the checker's
  upper-limb test.
* RF-src: the G sources are `RfSrc.gSrc`, the C1 lift sources `RfSrc.c1Src`,
  the H1 lift sources `RfSrc.h1Src`, each at a selected index whose
  one-index side conditions (eligibility, inactivity, `r ≠ 0`, `r ≠ 1023`)
  are hypotheses `hsel` the checker tests.
* RF-chain: `ιr = RfChain.iotaR`, `T = RfChain.chainTarget` (no premise).
* RF-round: reduced to `hrnd`, the Z4c coordinate closed form of each
  source's round image (`RfChain.rf_round_of_coords`).

Still premises (open): `rf_own`, `hrnd`, `rf_bat`, `rf_rel`, `rf_obs`,
`rf_col`. -/

set_option autoImplicit false

noncomputable section

namespace R1Z.CertR1Rf

open scoped BigOperators
open R0P R0Z.MaskLayout R0Z.HonestView R0Z.Partition R0Z.D12 R0Z.K4
open R1Z.Batched R1Z.VerifierRelationsR1 R1Z.PredicateR1 R1Z.CertSound R1Z.CertR1
open R1Z.RfDec R1Z.RfSrc R1Z.RfChain

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-- QueryCard for the decoded record: RF-dec is `rfl`. -/
theorem queryCard_of_decode (B : PackBasis F) (w : K) (raw : RawChallenges K F)
    (hl : raw.queries.length ≤ 22) : QueryCard (decode B w raw) :=
  queryCard_of_cert (decode B w raw) raw.queries (decode_queries B w raw) hl

/-- SemK4 for the decoded record from the upper-limb test (DESIGN-P-CERT §1.2). -/
theorem semK4_of_decode (B : PackBasis F) (hB : PackField B) (w : K) (raw : RawChallenges K F)
    (hup : ∀ (i : Fin 25) (k : Fin 4), raw.sem i (Fin.natAdd 4 k) = 0) :
    SemK4 B hB (decode B w raw) :=
  decode_semK4 B hB w raw hup

/-- HalfOK for the decoded record from the supplied inverse. -/
theorem halfOK_of_decode (B : PackBasis F) (w : K) (raw : RawChallenges K F) (y : K)
    (hy : (wideDecode B w (raw.sem 24) - 1 / 2) * y = 1) : HalfOK (decode B w raw) :=
  halfOK_of_cert (decode B w raw) y hy

/-- QPrime_R1 with RF-chain discharged and RF-round reduced to `hrnd`. -/
theorem qprime_of_cert_rf (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (hB : PackField B)
    (ch : Challenges K) (hsem : SemK4 B hB ch) {a N m : ℕ} (src : Fin N → M K F)
    (Own : Fin a → Fin N → F) (Rnd : Fin 1084 → Fin N → F)
    (ιo : (Fin a → F) →ₗ[F] Payload K R1Bat)
    (rf_own : ∀ t, R0Z.SilentReduction.ownMap (Bat := R1Bat) π B ch (src t) = ιo (col Own t))
    (hrnd : ∀ t, z4c (R0Z.Z4Maps.roundMaskMap (Bat := R1Bat) π B ch (src t)) =
      unflatL B (col Rnd t))
    (ents : Fin m → KerEntry N F) (Y : Fin 1084 → Fin m → F)
    (h : PreOK Own Rnd ents Y (chainTarget B hB (alpha ch))) : QPrime_R1 π B hB ch :=
  qprime_of_cert π B hB ch src Own Rnd ιo (iotaR B (alpha ch)) rf_own
    (rf_round_of_coords π B ch src Rnd hrnd) (chainTarget B hB (alpha ch))
    (rf_chain (Bat := R1Bat) B hB ch (fun j => hsem _)) ents Y h

/-- BCondG_R1 with RF-src discharged (G sources `gSrc`) and RF-round reduced. -/
theorem bcondG_of_cert_rf (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    {a₁ nb NG mG q r k : ℕ} (sel : Fin NG → Fin 1024 × Fin 4)
    (Z₁ : Fin a₁ → Fin NG → F) (Z₂ : Fin 1084 → Fin NG → F) (Bt : Fin nb → Fin NG → F)
    (ιo : (Fin a₁ → F) →ₗ[F] Payload K R1Bat)
    (ιb : (Fin nb → F) →ₗ[F] (R1Bat → K))
    (rf_own : ∀ t, R0Z.SilentReduction.ownMap (Bat := R1Bat) π B ch
      (gSrc (sel t).1 (sel t).2) = ιo (col Z₁ t))
    (hrnd : ∀ t, z4c (R0Z.Z4Maps.roundMaskMap (Bat := R1Bat) π B ch
      (gSrc (sel t).1 (sel t).2)) = unflatL B (col Z₂ t))
    (rf_bat : ∀ t, R0Z.SilentReduction.batMap (Bat := R1Bat) π B ch
      (gSrc (sel t).1 (sel t).2) = ιb (col Bt t))
    (Rel : Fin q → Fin nb → F)
    (rf_rel : ∀ x ∈ B0R1' (F := F) π ch,
      ∃ v : Fin nb → F, (∀ y, ∑ c, Rel y c * v c = 0) ∧ ιb v = x)
    (U : Fin r → Fin q → F) (piv : Fin r → Fin nb) (fr : Fin k → Fin nb)
    (hE : EchOK (Emat U Rel) piv fr)
    (ents : Fin mG → KerEntry NG F) (YG : Fin k → Fin mG → F)
    (h : PreOK₂ Z₁ Z₂ Bt ents YG (fun f => nvec (Emat U Rel) piv fr f)) :
    BCondG_R1 π B ch :=
  bcondG_of_cert π B ch (fun t => gSrc (sel t).1 (sel t).2)
    (fun t => gSrc_mem_Gonly (sel t).1 (sel t).2) Z₁ Z₂ Bt ιo (iotaR B (alpha ch)) ιb rf_own
    (rf_round_of_coords π B ch _ Z₂ hrnd) rf_bat Rel rf_rel U piv fr hE ents YG h

/-- C1Lift_c with RF-src discharged (sources `c1Src` at selected eligible rows). -/
theorem c1lift_of_cert_rf (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    (c : Fin 16) {w : ℕ} (sel : Fin w → Fin 1024)
    (hsel : ∀ t, eligible (Fin.castLE (by omega) c) (sel t) ∧ sel t ≠ 1023)
    (ι : (Fin w → F) →ₗ[F] (OwnCell → K))
    (rf_obs : (Wsem (K := K) (F := F)).map
      (obs (Bat := R1Bat) π B ch (Fin.castLE (by omega) c)) ≤ LinearMap.range ι)
    (O : Fin w → Fin w → F)
    (rf_col : ∀ t, obs (Bat := R1Bat) π B ch (Fin.castLE (by omega) c) (c1Src (sel t)) =
      ι (col O t))
    (U : Fin w → Fin w → F) (h : RinvOK O U) : C1Lift (Bat := R1Bat) π B ch c :=
  c1lift_of_cert π B ch c (fun t => c1Src (sel t))
    (fun t => c1Src_mem_Vsem _ c.isLt (sel t) (hsel t).1 (hsel t).2)
    ι rf_obs O rf_col U h

/-- H1Lift with RF-src discharged (sources `h1Src` at selected inactive rows). -/
theorem h1lift_of_cert_rf (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (hB : PackField B)
    (ch : Challenges K) {w : ℕ} (sel : Fin w → Fin 1024 × Fin 4)
    (hsel : ∀ t, (sel t).1 ≠ 0 ∧ (sel t).1 ∈ copyInactiveRows)
    (ι : (Fin w → F) →ₗ[F] (OwnCell → K))
    (rf_obs : (Wh1 B hB).map (obs (Bat := R1Bat) π B ch 26) ≤ LinearMap.range ι)
    (O : Fin w → Fin w → F)
    (rf_col : ∀ t, obs (Bat := R1Bat) π B ch 26 (h1Src B (sel t).1 (sel t).2) = ι (col O t))
    (U : Fin w → Fin w → F) (h : RinvOK O U) : H1Lift (Bat := R1Bat) π B hB ch :=
  h1lift_of_cert π B hB ch (fun t => h1Src B (sel t).1 (sel t).2)
    (fun t => h1Src_mem_Ph1 B (sel t).1 (sel t).2 (hsel t).1 (hsel t).2) ι rf_obs O rf_col U h

/-- Assembly on the decoded challenge record: HalfOK, SemK4 and QueryCard from
the record's own checks; the four certificate conjuncts from the `_rf`
theorems above. -/
theorem p_r1_of_decode (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (hB : PackField B) (w : K)
    (raw : RawChallenges K F) (y : K)
    (hy : (wideDecode B w (raw.sem 24) - 1 / 2) * y = 1)
    (hup : ∀ (i : Fin 25) (k : Fin 4), raw.sem i (Fin.natAdd 4 k) = 0)
    (hl : raw.queries.length ≤ 22)
    (hQ : SemK4 B hB (decode B w raw) → QPrime_R1 π B hB (decode B w raw))
    (hG : BCondG_R1 π B (decode B w raw))
    (hC1 : ∀ c : Fin 16, C1Lift (Bat := R1Bat) π B (decode B w raw) c)
    (hH1 : H1Lift (Bat := R1Bat) π B hB (decode B w raw)) :
    P_R1 π B hB (decode B w raw) :=
  p_r1_of_cert π B hB (decode B w raw) (halfOK_of_decode B w raw y hy)
    (semK4_of_decode B hB w raw hup) (hQ (semK4_of_decode B hB w raw hup)) hG hC1 hH1
    (queryCard_of_decode B w raw hl)

#print axioms queryCard_of_decode
#print axioms semK4_of_decode
#print axioms halfOK_of_decode
#print axioms qprime_of_cert_rf
#print axioms bcondG_of_cert_rf
#print axioms c1lift_of_cert_rf
#print axioms h1lift_of_cert_rf
#print axioms p_r1_of_decode

end R1Z.CertR1Rf

end
