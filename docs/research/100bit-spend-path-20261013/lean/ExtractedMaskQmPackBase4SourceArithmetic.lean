import ExtractedMaskReducerOps
import ExtractedMaskReducer
import Qm31PackBase4Slice
import ExtractedMaskQmPackBase4Arithmetic

/-! Source-order checked arithmetic for one accumulator of the current
generated `qm31_pack_base4`. The operation body below is copied in source
order from the exact G declaration slice. The array/copy adapter and the other
three output coordinates remain separate components. -/
set_option autoImplicit false
namespace AspisR1.ExtractedMaskQmPackBase4SourceArithmetic

open Aeneas.Std Result
open AspisR1.ExtractedMaskQmPackBase4Arithmetic
open AspisR1.ExtractedMaskReducerOps

abbrev P : Nat := AspisV8R15.ExactTowerBase.P

/-- Generated c0.a operations, with the already widened operands explicit. -/
def sourceC0a (p a b c d e f : U64) : Result U64 := do
  let i4 ← UScalar.sub p b
  let i5 ← UScalar.add a i4
  let i7 ← UScalar.mul (2#u64) c
  let i8 ← UScalar.add i5 i7
  let i10 ← UScalar.sub p d
  let i11 ← UScalar.add i8 i10
  let i13 ← UScalar.sub p e
  let i14 ← UScalar.add i11 i13
  let i15 ← UScalar.mul (2#u64) p
  let i17 ← UScalar.mul (2#u64) f
  let i18 ← UScalar.sub i15 i17
  UScalar.add i14 i18

/-- Generated c0.b operations in source order. -/
def sourceC0b (p a b c d e f : U64) : Result U64 := do
  let i21 ← UScalar.add a b
  let i22 ← UScalar.add i21 c
  let i23 ← UScalar.mul (2#u64) d
  let i24 ← UScalar.add i22 i23
  let i25 ← UScalar.mul (2#u64) e
  let i26 ← UScalar.add i24 i25
  let i27 ← UScalar.sub p f
  UScalar.add i26 i27

/-- Generated c1.a operations in source order. -/
def sourceC1a (p a b c d : U64) : Result U64 := do
  let i30 ← UScalar.sub p b
  let i31 ← UScalar.add a i30
  let i33 ← UScalar.add i31 c
  let i35 ← UScalar.sub p d
  UScalar.add i33 i35

/-- Generated c1.b operations in source order. -/
def sourceC1b (a b c d : U64) : Result U64 := do
  let i38 ← UScalar.add a b
  let i40 ← UScalar.add i38 c
  UScalar.add i40 d

theorem sourceC0a_success (p a b c d e f : U64)
    (hp : p.val = P)
    (ha : a.val < P) (hb : b.val < P) (hc : c.val < P)
    (hd : d.val < P) (he : e.val < P) (hf : f.val < P) :
    ∃ z : U64, sourceC0a p a b c d e f = .ok z ∧
      z.val = a.val + (P - b.val) + 2*c.val + (P - d.val) +
        (P - e.val) + (2*P - 2*f.val) := by
  have hp64 : p.val < 2^64 := by rw [hp]; norm_num [P]
  have htwo : (2#u64).val = 2 := rfl
  have ha64 : a.val < 2^64 := by norm_num [P] at ha ⊢ <;> omega
  have hb64 : b.val < 2^64 := by norm_num [P] at hb ⊢ <;> omega
  have hc64 : c.val < 2^64 := by norm_num [P] at hc ⊢ <;> omega
  have hd64 : d.val < 2^64 := by norm_num [P] at hd ⊢ <;> omega
  have he64 : e.val < 2^64 := by norm_num [P] at he ⊢ <;> omega
  have hf64 : f.val < 2^64 := by norm_num [P] at hf ⊢ <;> omega
  have h2p64 : 2*p.val < 2^64 := by rw [hp]; norm_num [P]
  obtain ⟨i4, hi4, hv4⟩ := sub_success p b (by rw [hp]; omega)
  have h5bound : a.val + (p.val-b.val) < 2^64 := by rw [hp]; norm_num [P] at ha hb ⊢ <;> omega
  obtain ⟨i5, hi5, hv5⟩ := add_success a i4 (by rw [hv4]; exact h5bound)
  have h7bound : 2*c.val < 2^64 := by norm_num [P] at hc ⊢ <;> omega
  obtain ⟨i7, hi7, hv7⟩ := mul_success (2#u64) c (by simpa using h7bound)
  have h8bound : a.val + (p.val-b.val) + 2*c.val < 2^64 := by rw [hp]; norm_num [P] at ha hb hc ⊢ <;> omega
  obtain ⟨i8, hi8, hv8⟩ := add_success i5 i7 (by rw [hv5, hv4, hv7]; exact h8bound)
  obtain ⟨i10, hi10, hv10⟩ := sub_success p d (by rw [hp]; omega)
  have h11bound : a.val + (p.val-b.val) + 2*c.val + (p.val-d.val) < 2^64 := by rw [hp]; norm_num [P] at ha hb hc hd ⊢ <;> omega
  obtain ⟨i11, hi11, hv11⟩ := add_success i8 i10 (by
    rw [hv8, hv5, hv4, hv7, hv10]; exact h11bound)
  obtain ⟨i13, hi13, hv13⟩ := sub_success p e (by rw [hp]; omega)
  have h14bound : a.val + (p.val-b.val) + 2*c.val + (p.val-d.val) + (p.val-e.val) < 2^64 := by rw [hp]; norm_num [P] at ha hb hc hd he ⊢ <;> omega
  obtain ⟨i14, hi14, hv14⟩ := add_success i11 i13 (by
    rw [hv11, hv8, hv5, hv4, hv7, hv10, hv13]; exact h14bound)
  obtain ⟨i15, hi15, hv15⟩ := mul_success (2#u64) p (by rw [hp]; norm_num [P])
  have h17bound : 2*f.val < 2^64 := by norm_num [P] at hf ⊢ <;> omega
  obtain ⟨i17, hi17, hv17⟩ := mul_success (2#u64) f (by simpa using h17bound)
  obtain ⟨i18, hi18, hv18⟩ := sub_success i15 i17 (by rw [hv15, hv17, htwo, hp]; omega)
  have hfinal : a.val + (P-b.val) + 2*c.val + (P-d.val) +
      (P-e.val) + (2*P-2*f.val) < 2^64 := by
    have hbnd : a.val + (P-b.val) + 2*c.val + (P-d.val) +
      (P-e.val) + (2*P-2*f.val) < 8*P := by omega
    norm_num [P] at hbnd ⊢ <;> omega
  obtain ⟨z, hz, hvz⟩ := add_success i14 i18 (by
    rw [hv14, hv11, hv8, hv5, hv4, hv7, hv10, hv13, hv18, hv15, hv17, htwo, hp]
    exact hfinal)
  refine ⟨z, ?_, ?_⟩
  · simp only [sourceC0a, hi4, hi5, hi7, hi8, hi10, hi11, hi13,
      hi14, hi15, hi17, hi18, hz, bind_tc_ok]
  · rw [hvz, hv14, hv11, hv8, hv5, hv4, hv7, hv10, hv13,
      hv18, hv15, hv17, htwo, hp]

theorem sourceC0b_success (p a b c d e f : U64)
    (hp : p.val = P)
    (ha : a.val < P) (hb : b.val < P) (hc : c.val < P)
    (hd : d.val < P) (he : e.val < P) (hf : f.val < P) :
    ∃ z : U64, sourceC0b p a b c d e f = .ok z ∧
      z.val = a.val + b.val + c.val + 2*d.val + 2*e.val + (P-f.val) := by
  have h64 (x : U64) (hx : x.val < P) : x.val < 2^64 := by
    norm_num [P] at hx ⊢ <;> omega
  have hp64 : p.val < 2^64 := by rw [hp]; norm_num [P]
  have ha64 := h64 a ha
  have hb64 := h64 b hb
  have hc64 := h64 c hc
  have hd64 := h64 d hd
  have he64 := h64 e he
  have hf64 := h64 f hf
  have h21bound : a.val + b.val < 2^64 := by norm_num [P] at ha hb ⊢ <;> omega
  obtain ⟨i21, h21, v21⟩ := add_success a b h21bound
  have h22bound : a.val + b.val + c.val < 2^64 := by norm_num [P] at ha hb hc ⊢ <;> omega
  obtain ⟨i22, h22, v22⟩ := add_success i21 c (by rw [v21]; exact h22bound)
  have h23bound : 2*d.val < 2^64 := by norm_num [P] at hd ⊢ <;> omega
  obtain ⟨i23, h23, v23⟩ := mul_success (2#u64) d (by simpa using h23bound)
  have h24bound : a.val + b.val + c.val + 2*d.val < 2^64 := by norm_num [P] at ha hb hc hd ⊢ <;> omega
  obtain ⟨i24, h24, v24⟩ := add_success i22 i23 (by rw [v22, v21, v23]; exact h24bound)
  have h25bound : 2*e.val < 2^64 := by norm_num [P] at he ⊢ <;> omega
  obtain ⟨i25, h25, v25⟩ := mul_success (2#u64) e (by simpa using h25bound)
  have h26bound : a.val + b.val + c.val + 2*d.val + 2*e.val < 2^64 := by norm_num [P] at ha hb hc hd he ⊢ <;> omega
  obtain ⟨i26, h26, v26⟩ := add_success i24 i25 (by rw [v24, v22, v21, v23, v25]; exact h26bound)
  obtain ⟨i27, h27, v27⟩ := sub_success p f (by rw [hp]; omega)
  have hfinal : a.val + b.val + c.val + 2*d.val + 2*e.val + (P-f.val) < 2^64 := by
    have hbnd : a.val + b.val + c.val + 2*d.val + 2*e.val + (P-f.val) < 8*P := by omega
    norm_num [P] at hbnd ⊢ <;> omega
  obtain ⟨z, hz, vz⟩ := add_success i26 i27 (by rw [v26, v24, v22, v21, v23, v25, v27, hp]; exact hfinal)
  refine ⟨z, ?_, ?_⟩
  · simp only [sourceC0b, h21, h22, h23, h24, h25, h26, h27, hz, bind_tc_ok]
  · rw [vz, v26, v25, v24, v23, v22, v21, v27]
    simp only [show (2#u64).val = 2 from rfl]
    omega

theorem sourceC1a_success (p a b c d : U64)
    (hp : p.val = P)
    (ha : a.val < P) (hb : b.val < P) (hc : c.val < P) (hd : d.val < P) :
    ∃ z : U64, sourceC1a p a b c d = .ok z ∧
      z.val = a.val + (P-b.val) + c.val + (P-d.val) := by
  have h64 (x : U64) (hx : x.val < P) : x.val < 2^64 := by
    norm_num [P] at hx ⊢ <;> omega
  have hp64 : p.val < 2^64 := by rw [hp]; norm_num [P]
  have ha64 := h64 a ha
  have hb64 := h64 b hb
  have hc64 := h64 c hc
  have hd64 := h64 d hd
  obtain ⟨i30, h30, v30⟩ := sub_success p b (by rw [hp]; omega)
  have h31b : a.val + (P-b.val) < 2^64 := by norm_num [P] at ha hb ⊢ <;> omega
  obtain ⟨i31, h31, v31⟩ := add_success a i30 (by rw [v30, hp]; exact h31b)
  have h33b : a.val + (P-b.val) + c.val < 2^64 := by norm_num [P] at ha hb hc ⊢ <;> omega
  obtain ⟨i33, h33, v33⟩ := add_success i31 c (by rw [v31, v30, hp]; exact h33b)
  obtain ⟨i35, h35, v35⟩ := sub_success p d (by rw [hp]; omega)
  have hfinal : a.val + (P-b.val) + c.val + (P-d.val) < 2^64 := by
    have hbnd : a.val + (P-b.val) + c.val + (P-d.val) < 4*P := by omega
    norm_num [P] at hbnd ⊢ <;> omega
  obtain ⟨z, hz, vz⟩ := add_success i33 i35 (by rw [v33, v31, v30, v35, hp]; exact hfinal)
  refine ⟨z, ?_, ?_⟩
  · simp only [sourceC1a, h30, h31, h33, h35, hz, bind_tc_ok]
  · rw [vz, v33, v35, v31, v30, hp]

theorem sourceC1b_success (a b c d : U64)
    (ha : a.val < P) (hb : b.val < P)
    (hc : c.val < P) (hd : d.val < P) :
    ∃ z : U64, sourceC1b a b c d = .ok z ∧
      z.val = a.val + b.val + c.val + d.val := by
  have h64 (x : U64) (hx : x.val < P) : x.val < 2^64 := by
    norm_num [P] at hx ⊢ <;> omega
  have ha64 := h64 a ha
  have hb64 := h64 b hb
  have hc64 := h64 c hc
  have hd64 := h64 d hd
  have h38b : a.val + b.val < 2^64 := by norm_num [P] at ha hb ⊢ <;> omega
  obtain ⟨i38, h38, v38⟩ := add_success a b (by exact h38b)
  have h40b : a.val + b.val + c.val < 2^64 := by norm_num [P] at ha hb hc ⊢ <;> omega
  obtain ⟨i40, h40, v40⟩ := add_success i38 c (by rw [v38]; exact h40b)
  have hfinal : a.val + b.val + c.val + d.val < 2^64 := by
    have hbnd : a.val + b.val + c.val + d.val < 4*P := by omega
    norm_num [P] at hbnd ⊢ <;> omega
  obtain ⟨z, hz, vz⟩ := add_success i40 d (by rw [v40, v38]; exact hfinal)
  refine ⟨z, ?_, ?_⟩
  · simp only [sourceC1b, h38, h40, hz, bind_tc_ok]
  · rw [vz, v40, v38]

theorem sourceC0a_reduces (p a b c d e f : U64)
    (hp : p.val = P)
    (ha : a.val < P) (hb : b.val < P) (hc : c.val < P)
    (hd : d.val < P) (he : e.val < P) (hf : f.val < P) :
    ∃ raw : U64,
      sourceC0a p a b c d e f = .ok raw ∧
      ∃ out : AspisR1SelectedMaskProbe.field.M31,
        AspisR1SelectedMaskProbe.field.M31.reduce_u64 raw = .ok out ∧
        out.val = (a.val + (P-b.val) + 2*c.val + (P-d.val) +
          (P-e.val) + (2*P-2*f.val)) % P ∧ out.val < P := by
  obtain ⟨raw, hraw, hval⟩ := sourceC0a_success p a b c d e f hp ha hb hc hd he hf
  obtain ⟨out, hout, hmod, hcanonical⟩ :=
    AspisR1.ExtractedMaskReducer.current_wrapper_mod raw
  refine ⟨raw, hraw, out, hout, ?_, hcanonical⟩
  calc
    out.val = raw.val % P := by simpa [P, AspisV8R17.RawReducer.P] using hmod
    _ = (a.val + (P-b.val) + 2*c.val + (P-d.val) +
        (P-e.val) + (2*P-2*f.val)) % P := by rw [hval]

/-- The actual Rust conversion closure used for every source limb is the U64
widening of the stored M31 word. -/
theorem limb_call_exact (x : AspisR1SelectedMaskProbe.field.M31) :
    AspisR1SelectedMaskProbe.field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call () x =
      .ok (UScalar.cast .U64 x) := by
  change Result.ok (Aeneas.Std.core.convert.num.FromU64U32.from x) =
    Result.ok (UScalar.cast .U64 x)
  congr 1

def sourceP64 : U64 :=
  Aeneas.Std.core.convert.num.FromU64U32.from
    AspisR1SelectedMaskProbe.field.P

theorem sourceP64_val : sourceP64.val = P := by
  rw [sourceP64, Aeneas.Std.core.convert.num.FromU64U32.from_val_eq]
  change AspisR1SelectedMaskProbe.field.P.val = P
  rw [AspisR1SelectedMaskProbe.field.P]
  rfl

/-- Canonical QM31 inputs make each widened limb a valid source c0.a input;
the theorem retains the four-input parameterization to match the generated
function's reads without choosing a concrete Slice representation. -/
theorem sourceC0a_qm_limbs (v : Fin 4 → AspisR1.ExtractedMaskQM31Exact.CurrentQM)
    (hv : ∀ j, AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM (v j)) :
    ∃ raw : U64,
      sourceC0a sourceP64
        (UScalar.cast .U64 (v 0).c0.a)
        (UScalar.cast .U64 (v 1).c0.b)
        (UScalar.cast .U64 (v 2).c1.a)
        (UScalar.cast .U64 (v 2).c1.b)
        (UScalar.cast .U64 (v 3).c1.a)
        (UScalar.cast .U64 (v 3).c1.b) = .ok raw ∧
      raw.val = (v 0).c0.a.val + (P-(v 1).c0.b.val) +
        2*(v 2).c1.a.val + (P-(v 2).c1.b.val) +
        (P-(v 3).c1.a.val) + (2*P-2*(v 3).c1.b.val) := by
  have hlimb (i : Fin 4) (j : Fin 4) :
      AspisR1.ExtractedMaskQmPackBase4Arithmetic.limb (v i) j < P :=
    limb_lt_P (v i) (hv i) j
  have h00 := hlimb 0 0
  have h11 := hlimb 1 1
  have h22 := hlimb 2 2
  have h23 := hlimb 2 3
  have h32 := hlimb 3 2
  have h33 := hlimb 3 3
  have hcast (x : AspisR1SelectedMaskProbe.field.M31) :
      (UScalar.cast .U64 x).val = x.val :=
    AspisR1.ExtractedMaskReducer.cast_widen_value x
  have h00' : (v 0).c0.a.val < P := by simpa [limb] using h00
  have h11' : (v 1).c0.b.val < P := by simpa [limb] using h11
  have h22' : (v 2).c1.a.val < P := by simpa [limb] using h22
  have h23' : (v 2).c1.b.val < P := by simpa [limb] using h23
  have h32' : (v 3).c1.a.val < P := by simpa [limb] using h32
  have h33' : (v 3).c1.b.val < P := by simpa [limb] using h33
  obtain ⟨raw, hraw, hval⟩ := sourceC0a_success sourceP64
    (UScalar.cast .U64 (v 0).c0.a)
    (UScalar.cast .U64 (v 1).c0.b)
    (UScalar.cast .U64 (v 2).c1.a)
    (UScalar.cast .U64 (v 2).c1.b)
    (UScalar.cast .U64 (v 3).c1.a)
    (UScalar.cast .U64 (v 3).c1.b)
    sourceP64_val (by simpa [hcast] using h00') (by simpa [hcast] using h11')
    (by simpa [hcast] using h22') (by simpa [hcast] using h23')
    (by simpa [hcast] using h32') (by simpa [hcast] using h33')
  refine ⟨raw, hraw, ?_⟩
  simpa only [hcast] using hval

/-- The four source-order checked accumulator fragments succeed on four
canonical QM31 words. Their raw values are exactly the four Nat formulas
whose simultaneous field interpretation was proved above. -/
theorem source_accumulators_qm_limbs
    (v : Fin 4 → AspisR1.ExtractedMaskQM31Exact.CurrentQM)
    (hv : ∀ j, AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM (v j)) :
    ∃ r00 r01 r10 r11 : U64,
      sourceC0a sourceP64
        (UScalar.cast .U64 (v 0).c0.a) (UScalar.cast .U64 (v 1).c0.b)
        (UScalar.cast .U64 (v 2).c1.a) (UScalar.cast .U64 (v 2).c1.b)
        (UScalar.cast .U64 (v 3).c1.a) (UScalar.cast .U64 (v 3).c1.b) = .ok r00 ∧
      r00.val = acc00 v ∧
      sourceC0b sourceP64
        (UScalar.cast .U64 (v 0).c0.b) (UScalar.cast .U64 (v 1).c0.a)
        (UScalar.cast .U64 (v 2).c1.a) (UScalar.cast .U64 (v 2).c1.b)
        (UScalar.cast .U64 (v 3).c1.a) (UScalar.cast .U64 (v 3).c1.b) = .ok r01 ∧
      r01.val = acc01 v ∧
      sourceC1a sourceP64
        (UScalar.cast .U64 (v 0).c1.a) (UScalar.cast .U64 (v 1).c1.b)
        (UScalar.cast .U64 (v 2).c0.a) (UScalar.cast .U64 (v 3).c0.b) = .ok r10 ∧
      r10.val = acc10 v ∧
      sourceC1b
        (UScalar.cast .U64 (v 0).c1.b) (UScalar.cast .U64 (v 1).c1.a)
        (UScalar.cast .U64 (v 2).c0.b) (UScalar.cast .U64 (v 3).c0.a) = .ok r11 ∧
      r11.val = acc11 v := by
  obtain ⟨r00, h00, v00⟩ := sourceC0a_qm_limbs v hv
  have hlimb (i : Fin 4) (j : Fin 4) :
      AspisR1.ExtractedMaskQmPackBase4Arithmetic.limb (v i) j < P :=
    limb_lt_P (v i) (hv i) j
  have hcast (x : AspisR1SelectedMaskProbe.field.M31) :
      (UScalar.cast .U64 x).val = x.val :=
    AspisR1.ExtractedMaskReducer.cast_widen_value x
  have h0 : (UScalar.cast .U64 (v 0).c0.b).val < P := by
    rw [hcast]; exact hlimb 0 1
  have h1 : (UScalar.cast .U64 (v 1).c0.a).val < P := by
    rw [hcast]; exact hlimb 1 0
  have h2 : (UScalar.cast .U64 (v 2).c1.a).val < P := by
    rw [hcast]; exact hlimb 2 2
  have h3 : (UScalar.cast .U64 (v 2).c1.b).val < P := by
    rw [hcast]; exact hlimb 2 3
  have h4 : (UScalar.cast .U64 (v 3).c1.a).val < P := by
    rw [hcast]; exact hlimb 3 2
  have h5 : (UScalar.cast .U64 (v 3).c1.b).val < P := by
    rw [hcast]; exact hlimb 3 3
  obtain ⟨r01, h01, v01⟩ := sourceC0b_success sourceP64
    (UScalar.cast .U64 (v 0).c0.b) (UScalar.cast .U64 (v 1).c0.a)
    (UScalar.cast .U64 (v 2).c1.a) (UScalar.cast .U64 (v 2).c1.b)
    (UScalar.cast .U64 (v 3).c1.a) (UScalar.cast .U64 (v 3).c1.b)
    sourceP64_val h0 h1 h2 h3 h4 h5
  have h6 : (UScalar.cast .U64 (v 0).c1.a).val < P := by
    rw [hcast]; exact hlimb 0 2
  have h7 : (UScalar.cast .U64 (v 1).c1.b).val < P := by
    rw [hcast]; exact hlimb 1 3
  have h8 : (UScalar.cast .U64 (v 2).c0.a).val < P := by
    rw [hcast]; exact hlimb 2 0
  have h9 : (UScalar.cast .U64 (v 3).c0.b).val < P := by
    rw [hcast]; exact hlimb 3 1
  obtain ⟨r10, h10, v10⟩ := sourceC1a_success sourceP64
    (UScalar.cast .U64 (v 0).c1.a) (UScalar.cast .U64 (v 1).c1.b)
    (UScalar.cast .U64 (v 2).c0.a) (UScalar.cast .U64 (v 3).c0.b)
    sourceP64_val h6 h7 h8 h9
  have h11 : (UScalar.cast .U64 (v 0).c1.b).val < P := by
    rw [hcast]; exact hlimb 0 3
  have h12 : (UScalar.cast .U64 (v 1).c1.a).val < P := by
    rw [hcast]; exact hlimb 1 2
  have h13 : (UScalar.cast .U64 (v 2).c0.b).val < P := by
    rw [hcast]; exact hlimb 2 1
  have h14 : (UScalar.cast .U64 (v 3).c0.a).val < P := by
    rw [hcast]; exact hlimb 3 0
  obtain ⟨r11, h11s, v11⟩ := sourceC1b_success
    (UScalar.cast .U64 (v 0).c1.b) (UScalar.cast .U64 (v 1).c1.a)
    (UScalar.cast .U64 (v 2).c0.b) (UScalar.cast .U64 (v 3).c0.a)
    h11 h12 h13 h14
  refine ⟨r00, r01, r10, r11, h00, ?_, h01, ?_, h10, ?_, h11s, ?_⟩
  · simpa [acc00, AspisR1.ExtractedMaskQmPackBase4Arithmetic.limb, hcast] using v00
  · simpa [acc01, AspisR1.ExtractedMaskQmPackBase4Arithmetic.limb, hcast] using v01
  · simpa [acc10, AspisR1.ExtractedMaskQmPackBase4Arithmetic.limb, hcast] using v10
  · simpa [acc11, AspisR1.ExtractedMaskQmPackBase4Arithmetic.limb, hcast] using v11

theorem source_accumulators_reduce
    (v : Fin 4 → AspisR1.ExtractedMaskQM31Exact.CurrentQM)
    (hv : ∀ j, AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM (v j)) :
    ∃ raw00 raw01 raw10 raw11 : U64,
      (∃ out00 : AspisR1SelectedMaskProbe.field.M31,
        AspisR1SelectedMaskProbe.field.M31.reduce_u64 raw00 = .ok out00 ∧
        out00.val = (acc00 v) % P ∧ out00.val < P) ∧
      (∃ out01 : AspisR1SelectedMaskProbe.field.M31,
        AspisR1SelectedMaskProbe.field.M31.reduce_u64 raw01 = .ok out01 ∧
        out01.val = (acc01 v) % P ∧ out01.val < P) ∧
      (∃ out10 : AspisR1SelectedMaskProbe.field.M31,
        AspisR1SelectedMaskProbe.field.M31.reduce_u64 raw10 = .ok out10 ∧
        out10.val = (acc10 v) % P ∧ out10.val < P) ∧
      (∃ out11 : AspisR1SelectedMaskProbe.field.M31,
        AspisR1SelectedMaskProbe.field.M31.reduce_u64 raw11 = .ok out11 ∧
        out11.val = (acc11 v) % P ∧ out11.val < P) := by
  obtain ⟨raw00, raw01, raw10, raw11, h00, v00, h01, v01,
      h10, v10, h11, v11⟩ := source_accumulators_qm_limbs v hv
  obtain ⟨out00, r00, m00, c00⟩ :=
    AspisR1.ExtractedMaskReducer.current_wrapper_mod raw00
  obtain ⟨out01, r01, m01, c01⟩ :=
    AspisR1.ExtractedMaskReducer.current_wrapper_mod raw01
  obtain ⟨out10, r10, m10, c10⟩ :=
    AspisR1.ExtractedMaskReducer.current_wrapper_mod raw10
  obtain ⟨out11, r11, m11, c11⟩ :=
    AspisR1.ExtractedMaskReducer.current_wrapper_mod raw11
  refine ⟨raw00, raw01, raw10, raw11, ?_⟩
  refine ⟨⟨out00, r00, ?_, c00⟩,
    ⟨⟨out01, r01, ?_, c01⟩,
      ⟨⟨out10, r10, ?_, c10⟩, ⟨out11, r11, ?_, c11⟩⟩⟩⟩
  · simpa [v00, P, AspisV8R17.RawReducer.P] using m00
  · simpa [v01, P, AspisV8R17.RawReducer.P] using m01
  · simpa [v10, P, AspisV8R17.RawReducer.P] using m10
  · simpa [v11, P, AspisV8R17.RawReducer.P] using m11

/-- The four source-order checked accumulators and reducer calls assemble to a
canonical value with the exact tower basis result. This theorem composes the
four arithmetic fragments, but not the generated Slice/array wrapper. -/
theorem checked_source_coordinates_pack
    (v : Fin 4 → AspisR1.ExtractedMaskQM31Exact.CurrentQM)
    (hv : ∀ j, AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM (v j)) :
    ∃ out : AspisR1.ExtractedMaskQM31Exact.CurrentQM,
      AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM out ∧
      AspisR1.ExtractedMaskQM31Exact.decode out = mathematicalPack v := by
  obtain ⟨raw00, raw01, raw10, raw11,
      ⟨out00, hr00, hv00, hc00⟩,
      ⟨out01, hr01, hv01, hc01⟩,
      ⟨out10, hr10, hv10, hc10⟩,
      ⟨out11, hr11, hv11, hc11⟩⟩ := source_accumulators_reduce v hv
  let out : AspisR1.ExtractedMaskQM31Exact.CurrentQM :=
    ⟨⟨out00, out01⟩, ⟨out10, out11⟩⟩
  have hout : AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM out :=
    ⟨⟨hc00, hc01⟩, ⟨hc10, hc11⟩⟩
  have hdecode : AspisR1.ExtractedMaskQM31Exact.decode out = accumulatorPack v := by
    simpa [out] using reducedOutput_decode_eq_accumulatorPack v
      out00 out01 out10 out11 hv00 hv01 hv10 hv11
  refine ⟨out, hout, ?_⟩
  rw [hdecode, mathematicalPack_eq_accumulatorPack v hv]

#print axioms sourceC0a_success
#print axioms sourceC0b_success
#print axioms sourceC1a_success
#print axioms sourceC1b_success
#print axioms sourceC0a_reduces
#print axioms limb_call_exact
#print axioms sourceP64_val
#print axioms sourceC0a_qm_limbs
#print axioms source_accumulators_qm_limbs
#print axioms source_accumulators_reduce
#print axioms checked_source_coordinates_pack
end AspisR1.ExtractedMaskQmPackBase4SourceArithmetic
