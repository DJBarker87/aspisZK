import R1Z.SamplerLawIface
import ExtractedQM31SamplerCorrect

/-! The D47.2 premise `QM31SamplerLaw` from the spend path's proved sampler facts
(DESIGN-BUILD-INTEGRATION §4 (c)).  Joint module: compiled on the spend-path sampler base
(pinned overlay qm31-index-sampler-correct-432-20261016, correct-c).

* carrier transport `arrEquiv : (Fin 32 → UInt8) ≃ Array U8 32#usize`, through the byte state
  `Fin 32 → Fin 256` and the spend path's `encodeState`/`decodeState` round trips;
* `s1Spend ι`: the extracted `qm31_sample` on the transported block, read through the current
  carrier `decode ∘ toCurrent` into `QM31Exact`, then through any injective `ι : QM31Exact → K`
  (the QM31 ↔ K transport);
* `rankE`: `SourceSamplerByteRank.rank ∘ arrEquiv` as an equivalence onto `Fin 2^256`;
* `qm31SamplerLaw_spend`: the interface law, from `ExtractedQM31SamplerCorrect.sample_total`,
  `SamplerNatModel.qm31Digits_value` and the digit canonicality, with no premise besides `ι`
  injective.  `SemRows01` (which decoder rows feed χ and λ) is a property of the wire, not of
  the sampler, and is not addressed here. -/

set_option autoImplicit false

noncomputable section

namespace R1J.SamplerLawSpend

open Aeneas Aeneas.Std

abbrev Ans := Fin 32 → UInt8
abbrev QF := AspisR1.ExtractedCurrentQM31Exact.QM31Exact
abbrev MF := AspisR1.ExtractedCurrentQM31Exact.M31Exact
abbrev Pm : ℕ := AspisR1.SamplerMachineBounds.P

/-! ## Carrier transport -/

def stateEquiv : Ans ≃ (Fin 32 → Fin 256) where
  toFun a := fun i => (a i).toFin
  invFun s := fun i => UInt8.ofFin (s i)
  left_inv a := by funext i; exact UInt8.ofFin_toFin (a i)
  right_inv s := by funext i; exact UInt8.toFin_ofFin (s i)

def stateArrEquiv : (Fin 32 → Fin 256) ≃ Array U8 32#usize where
  toFun := AspisV8R19.SqueezeOracleBridge.encodeState
  invFun := AspisV8R19.SqueezeOracleBridge.decodeState
  left_inv := AspisV8R19.SqueezeOracleBridge.state_roundtrip
  right_inv := AspisV8R19.SqueezeOracleBridge.array_roundtrip

def arrEquiv : Ans ≃ Array U8 32#usize := stateEquiv.trans stateArrEquiv

theorem pow_eq : (256 : ℕ) ^ 32 = 2 ^ 256 := by norm_num

def rankE : Ans ≃ Fin (2 ^ 256) :=
  (stateEquiv.trans R0C.ModuloField.blockRank).trans (finCongr pow_eq)

theorem rankE_val (a : Ans) :
    (rankE a).val = AspisR1.SourceSamplerByteRank.rank (arrEquiv a) := by
  show (R0C.ModuloField.blockRank (stateEquiv a)).val =
    (R0C.ModuloField.blockRank (AspisV8R19.SqueezeOracleBridge.decodeState
      (AspisV8R19.SqueezeOracleBridge.encodeState (stateEquiv a)))).val
  rw [AspisV8R19.SqueezeOracleBridge.state_roundtrip]

/-! ## The sampled value -/

/-- The actual extracted sampler on the transported block, through the current carrier. -/
def s1Spend {K : Type} (ι : QF → K) (a : Ans) : K :=
  match AspisR1Qm31SamplerIndex.sampler.qm31_sample (arrEquiv a) with
  | .ok q => ι (AspisR1.ExtractedCurrentQM31Exact.decode
      (AspisR1.ExtractedQM31SamplerCarrier.toCurrent q))
  | _ => ι 0

theorem s1Spend_ok {K : Type} (ι : QF → K) (a : Ans) :
    ∃ q, AspisR1Qm31SamplerIndex.sampler.qm31_sample (arrEquiv a) = .ok q ∧
      s1Spend ι a = ι (AspisR1.ExtractedCurrentQM31Exact.decode
        (AspisR1.ExtractedQM31SamplerCarrier.toCurrent q)) := by
  obtain ⟨q, hq, -, -⟩ := AspisR1.ExtractedQM31SamplerCorrect.sample_total (arrEquiv a)
  exact ⟨q, hq, by simp only [s1Spend, hq]⟩

/-! ## Digits -/

/-- The four low base-`p` digits read into the exact tower, c0.a/c0.b/c1.a/c1.b order. -/
def digitsQ (x : ℕ) : QF :=
  ⟨⟨((x % Pm : ℕ) : MF), ((x / Pm % Pm : ℕ) : MF)⟩,
    ⟨((x / Pm / Pm % Pm : ℕ) : MF), ((x / Pm / Pm / Pm % Pm : ℕ) : MF)⟩⟩

def emb {K : Type} (ι : QF → K) (x : ℕ) : K := ι (digitsQ x)

theorem lowDigits_mod (p : ℕ) :
    ∀ n x, AspisR1.SamplerNatModel.lowDigits p n (x % p ^ n) =
      AspisR1.SamplerNatModel.lowDigits p n x
  | 0, _ => rfl
  | n + 1, x => by
    show x % p ^ (n + 1) % p :: AspisR1.SamplerNatModel.lowDigits p n (x % p ^ (n + 1) / p) =
      x % p :: AspisR1.SamplerNatModel.lowDigits p n (x / p)
    rw [Nat.mod_mod_of_dvd x (dvd_pow_self p (Nat.succ_ne_zero n)), pow_succ',
      Nat.mod_mul_right_div_self, lowDigits_mod p n (x / p)]

theorem qm31Digits_mod (x : ℕ) :
    AspisR1.SamplerNatModel.qm31Digits (x % Pm ^ 4) = AspisR1.SamplerNatModel.qm31Digits x :=
  lowDigits_mod Pm 4 x

theorem qm31Digits_eq (x : ℕ) :
    AspisR1.SamplerNatModel.qm31Digits x =
      [x % Pm, x / Pm % Pm, x / Pm / Pm % Pm, x / Pm / Pm / Pm % Pm] := rfl

theorem Pm_eq : Pm = 2147483647 := by norm_num [Pm, AspisR1.SamplerMachineBounds.P]

theorem Pm_pos : 0 < Pm := by rw [Pm_eq]; norm_num

theorem cast_digit_inj {u v : ℕ} (hu : u < Pm) (hv : v < Pm)
    (h : ((u : ℕ) : MF) = ((v : ℕ) : MF)) : u = v := by
  have h' : u % 2147483647 = v % 2147483647 := (ZMod.natCast_eq_natCast_iff' u v 2147483647).mp h
  rw [Pm_eq] at hu hv
  rwa [Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv] at h'

theorem digitsQ_inj (x y : ℕ) (h : digitsQ x = digitsQ y) :
    AspisR1.SamplerNatModel.qm31Digits x = AspisR1.SamplerNatModel.qm31Digits y := by
  have h0 : ((x % Pm : ℕ) : MF) = ((y % Pm : ℕ) : MF) := congrArg (fun q : QF => q.re.re) h
  have h1 : ((x / Pm % Pm : ℕ) : MF) = ((y / Pm % Pm : ℕ) : MF) :=
    congrArg (fun q : QF => q.re.im) h
  have h2 : ((x / Pm / Pm % Pm : ℕ) : MF) = ((y / Pm / Pm % Pm : ℕ) : MF) :=
    congrArg (fun q : QF => q.im.re) h
  have h3 : ((x / Pm / Pm / Pm % Pm : ℕ) : MF) = ((y / Pm / Pm / Pm % Pm : ℕ) : MF) :=
    congrArg (fun q : QF => q.im.im) h
  rw [qm31Digits_eq, qm31Digits_eq,
    cast_digit_inj (Nat.mod_lt _ Pm_pos) (Nat.mod_lt _ Pm_pos) h0,
    cast_digit_inj (Nat.mod_lt _ Pm_pos) (Nat.mod_lt _ Pm_pos) h1,
    cast_digit_inj (Nat.mod_lt _ Pm_pos) (Nat.mod_lt _ Pm_pos) h2,
    cast_digit_inj (Nat.mod_lt _ Pm_pos) (Nat.mod_lt _ Pm_pos) h3]

theorem digitsQ_mod (x : ℕ) : digitsQ (x % Pm ^ 4) = digitsQ x := by
  have hm := qm31Digits_mod x
  rw [qm31Digits_eq, qm31Digits_eq] at hm
  simp only [List.cons.injEq] at hm
  obtain ⟨e0, e1, e2, e3, -⟩ := hm
  simp only [digitsQ, e0, e1, e2, e3]

theorem emb_inj {K : Type} (ι : QF → K) (hι : Function.Injective ι) (x y : ℕ)
    (hx : x < (2 ^ 31 - 1) ^ 4) (hy : y < (2 ^ 31 - 1) ^ 4) (h : emb ι x = emb ι y) :
    x = y := by
  have hd := digitsQ_inj x y (hι h)
  have hv := congrArg (AspisR1.SamplerAddDigits.digitsValue AspisR1.SamplerMachineBounds.P) hd
  rw [AspisR1.SamplerNatModel.qm31Digits_value, AspisR1.SamplerNatModel.qm31Digits_value] at hv
  have hP : AspisR1.SamplerMachineBounds.P = 2 ^ 31 - 1 := rfl
  rw [hP] at hv
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at hv

theorem decode_sample (q : AspisR1.ExtractedQM31SamplerCarrier.SamplerQM) (r : ℕ)
    (hv : AspisR1.ExtractedQM31SamplerCorrect.coordinates q =
      AspisR1.SamplerNatModel.qm31Digits r) :
    AspisR1.ExtractedCurrentQM31Exact.decode
      (AspisR1.ExtractedQM31SamplerCarrier.toCurrent q) = digitsQ r := by
  rw [qm31Digits_eq] at hv
  simp only [AspisR1.ExtractedQM31SamplerCorrect.coordinates, List.cons.injEq] at hv
  obtain ⟨h0, h1, h2, h3, -⟩ := hv
  show (⟨⟨((q.c0.a.val : ℕ) : MF), ((q.c0.b.val : ℕ) : MF)⟩,
    ⟨((q.c1.a.val : ℕ) : MF), ((q.c1.b.val : ℕ) : MF)⟩⟩ : QF) = digitsQ r
  rw [h0, h1, h2, h3]
  rfl

theorem sample {K : Type} (ι : QF → K) (a : Ans) :
    s1Spend ι a = emb ι ((rankE a).val % (2 ^ 31 - 1) ^ 4) := by
  obtain ⟨q, hq, -, hv⟩ := AspisR1.ExtractedQM31SamplerCorrect.sample_total (arrEquiv a)
  have hs : s1Spend ι a = ι (AspisR1.ExtractedCurrentQM31Exact.decode
      (AspisR1.ExtractedQM31SamplerCarrier.toCurrent q)) := by simp only [s1Spend, hq]
  have hP : (2 ^ 31 - 1 : ℕ) = Pm := rfl
  rw [hs, decode_sample q _ hv, emb, hP, digitsQ_mod, rankE_val]

/-- The D47.2 sampler law, from the spend path's sampler theorems. -/
def qm31SamplerLaw_spend {K : Type} (ι : QF → K) (hι : Function.Injective ι) :
    R1Z.SamplerLawIface.QM31SamplerLaw (s1Spend ι) where
  rank := rankE
  emb := emb ι
  emb_inj := emb_inj ι hι
  sample := sample ι

end R1J.SamplerLawSpend

#print axioms R1J.SamplerLawSpend.arrEquiv
#print axioms R1J.SamplerLawSpend.rankE_val
#print axioms R1J.SamplerLawSpend.s1Spend_ok
#print axioms R1J.SamplerLawSpend.lowDigits_mod
#print axioms R1J.SamplerLawSpend.digitsQ_inj
#print axioms R1J.SamplerLawSpend.digitsQ_mod
#print axioms R1J.SamplerLawSpend.decode_sample
#print axioms R1J.SamplerLawSpend.emb_inj
#print axioms R1J.SamplerLawSpend.sample
#print axioms R1J.SamplerLawSpend.qm31SamplerLaw_spend
