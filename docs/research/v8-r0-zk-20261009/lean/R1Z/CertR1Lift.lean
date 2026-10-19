import R1Z.CertR1Rf
import R1Z.RfObs

/-! D49.4 C2: the lift conjuncts with every row-formula premise discharged.

`C1Lift_c` and `H1Lift` follow from the checker's right-inverse test alone
(`RinvOK O U`), with `O` the lift column matrix `RfObs.colC1` / `colH1`
and `ι` = `RfObs.iotaC1` / `iotaH1` for the query list `l`.  The remaining
hypotheses are decoder facts — `ch.queries = l.toFinset` (RF-dec), α ∈ K₄
(SemK4), the two circle points in K₄ (the Rust `z` are QM31 points) — and the
one-index side conditions `hsel` of the selected sources.  The Rust-side
correspondence (that the extracted checker builds exactly `colC1`/`colH1`,
whose closed form is `RfObs.obs_balWord_*`) is C3. -/

set_option autoImplicit false

noncomputable section

namespace R1Z.CertR1Lift

open R0P R0Z.MaskLayout R0Z.HonestView R0Z.K4
open R1Z.Batched R1Z.PredicateR1 R1Z.CertSound R1Z.CertR1 R1Z.CertR1Rf
open R1Z.RfDec R1Z.RfSrc R1Z.RfObs

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

theorem c1lift_of_rinv (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (hB : PackField B)
    (ch : Challenges K) (l : List (Fin 262144)) (hq : ch.queries = l.toFinset)
    (hsem : SemK4 B hB ch)
    (hz : ∀ j, (ch.circle j).1.1 ∈ K4 B hB ∧ (ch.circle j).1.2 ∈ K4 B hB)
    (c : Fin 16) (sel : Fin (24 + 4 * l.length) → Fin 1024)
    (hsel : ∀ t, eligible (Fin.castLE (by omega) c) (sel t) ∧ sel t ≠ 1023)
    (U : Fin (24 + 4 * l.length) → Fin (24 + 4 * l.length) → F)
    (h : RinvOK (colC1 (Bat := R1Bat) B hB π ch (Fin.castLE (by omega) c) l sel) U) :
    C1Lift (Bat := R1Bat) π B ch c :=
  c1lift_of_cert_rf π B ch c sel hsel (iotaC1 B l)
    (rf_obs_C1 B hB π ch _ l hq (fun j => hsem _) hz) _
    (rf_col_C1 B hB π ch _ l hq (fun j => hsem _) hz sel) U h

theorem h1lift_of_rinv (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (hB : PackField B)
    (ch : Challenges K) (l : List (Fin 262144)) (hq : ch.queries = l.toFinset)
    (hsem : SemK4 B hB ch)
    (hz : ∀ j, (ch.circle j).1.1 ∈ K4 B hB ∧ (ch.circle j).1.2 ∈ K4 B hB)
    (sel : Fin (24 + 16 * l.length) → Fin 1024 × Fin 4)
    (hsel : ∀ t, (sel t).1 ≠ 0 ∧ (sel t).1 ∈ copyInactiveRows)
    (U : Fin (24 + 16 * l.length) → Fin (24 + 16 * l.length) → F)
    (h : RinvOK (colH1 (Bat := R1Bat) B hB π ch l sel) U) :
    H1Lift (Bat := R1Bat) π B hB ch :=
  h1lift_of_cert_rf π B hB ch sel hsel (iotaH1 B l)
    (rf_obs_H1 B hB π ch l hq (fun j => hsem _) hz) _
    (rf_col_H1 B hB π ch l hq (fun j => hsem _) hz sel) U h

/-- Assembly on the decoded record: HalfOK, SemK4, QueryCard from the record's
own checks, both lift conjuncts from right-inverse certificates alone; QPrime
and BCondG still carry their open premises (through `CertR1Rf`). -/
theorem p_r1_of_decode_lifts (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (hB : PackField B)
    (w : K) (raw : RawChallenges K F) (y : K)
    (hy : (wideDecode B w (raw.sem 24) - 1 / 2) * y = 1)
    (hup : ∀ (i : Fin 25) (k : Fin 4), raw.sem i (Fin.natAdd 4 k) = 0)
    (hl : raw.queries.length ≤ 22)
    (hz : ∀ j, (raw.circle j).1.1 ∈ K4 B hB ∧ (raw.circle j).1.2 ∈ K4 B hB)
    (hQ : SemK4 B hB (decode B w raw) → QPrime_R1 π B hB (decode B w raw))
    (hG : BCondG_R1 π B (decode B w raw))
    (sel1 : Fin 16 → Fin (24 + 4 * raw.queries.length) → Fin 1024)
    (hsel1 : ∀ c t, eligible (Fin.castLE (by omega) c) (sel1 c t) ∧ sel1 c t ≠ 1023)
    (U1 : Fin 16 → Fin (24 + 4 * raw.queries.length) → Fin (24 + 4 * raw.queries.length) → F)
    (h1 : ∀ c, RinvOK (colC1 (Bat := R1Bat) B hB π (decode B w raw) (Fin.castLE (by omega) c)
      raw.queries (sel1 c)) (U1 c))
    (selH : Fin (24 + 16 * raw.queries.length) → Fin 1024 × Fin 4)
    (hselH : ∀ t, (selH t).1 ≠ 0 ∧ (selH t).1 ∈ copyInactiveRows)
    (UH : Fin (24 + 16 * raw.queries.length) → Fin (24 + 16 * raw.queries.length) → F)
    (hH : RinvOK (colH1 (Bat := R1Bat) B hB π (decode B w raw) raw.queries selH) UH) :
    P_R1 π B hB (decode B w raw) :=
  p_r1_of_decode π B hB w raw y hy hup hl hQ hG
    (fun c => c1lift_of_rinv π B hB _ raw.queries (decode_queries B w raw)
      (semK4_of_decode B hB w raw hup) hz c (sel1 c) (hsel1 c) (U1 c) (h1 c))
    (h1lift_of_rinv π B hB _ raw.queries (decode_queries B w raw)
      (semK4_of_decode B hB w raw hup) hz selH hselH UH hH)

#print axioms c1lift_of_rinv
#print axioms h1lift_of_rinv
#print axioms p_r1_of_decode_lifts

end R1Z.CertR1Lift

end
