import EbyKPushActualRawCoefficientBoundsV10
import R22RawQmProductResiduesV15
import S5CanonicalProductRangesV1
import DotPushSuccessResidues
import EbyKPushDotBackend
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1EbyKPushDecodedProductUpdate

abbrev M := AspisR1.R22RawQmProductResidues.M
abbrev Q := AspisR1.R22RawQmProductResidues.Q
abbrev PushWide := AspisR1EbyKPushActualRawCoefficientBounds.PushWide
abbrev PushQm := AspisR1EbyKPushActualRawCoefficientBounds.PushQm
abbrev PushState := AspisR1EbyKPushActualRawCoefficientBounds.PushState
abbrev QRaw := AspisR1EbyKPushActualRawCoefficientBounds.QRaw

private theorem updated_sum_cast_update
    (s r : Array U64 4#usize)
    (hs : ∀ x ∈ s.val, x.val < 2^46) (j : Nat) (hj : j<4) :
    (((AspisR1DotPushLocal.Proof.updatedSums s r).val[j]'(by rw [(AspisR1DotPushLocal.Proof.updatedSums s r).property]; exact hj)).val : M) =
      ((s.val[j]'(by rw [s.property]; exact hj)).val : M) +
      ((r.val[j]'(by rw [r.property]; exact hj)).val : M) := by
  have hm := AspisR1DotPushLocal.Proof.updatedSums_residue s r hs j hj
  have hc := congrArg (fun n : Nat => (n : M)) hm
  simpa [AspisR1EbyKDotPushNatStep.modulus, AspisV8R17.RawReducer.P,
    ZMod.natCast_mod, Nat.cast_add] using hc

private theorem raw_array_cast_qmul
    (r : Array U64 4#usize) (a b c d e f g h : Nat)
    (x0 x1 x2 x3 : U64)
    (hshape : r = Array.make 4#usize [x0,x1,x2,x3])
    (h0 : x0.val = AspisR1.R22RawQmProductResidues.rawC0 a b c d e f g h)
    (h1 : x1.val = AspisR1.R22RawQmProductResidues.rawC1 a b c d e f g h)
    (h2 : x2.val = AspisR1.R22RawQmProductResidues.rawC2 a b c d e f g h)
    (h3 : x3.val = AspisR1.R22RawQmProductResidues.rawC3 a b c d e f g h)
    (ha : a≤2^31-2) (hb : b≤2^31-2) (hc : c≤2^31-2) (hd : d≤2^31-2)
    (he : e≤2^31-2) (hf : f≤2^31-2) (hg : g≤2^31-2) (hh : h≤2^31-2) :
    (((r.val[0]!).val : M),
     ((r.val[1]!).val : M),
     ((r.val[2]!).val : M),
     ((r.val[3]!).val : M)) =
      AspisR1.R22RawQmProductResidues.qmulCoefficients ((a,b),(c,d)) ((e,f),(g,h)) := by
  have guards := AspisR1S5CurrentRepin.canonical_raw_range_guards a b c d e f g h
    ha hb hc hd he hf hg hh
  dsimp only at guards
  rcases guards with ⟨_,hU,_,_,h0a,_,_,h0bFold,_,_,_,_,_,h2a,h2b,_,_,_,_⟩
  have hfold (n : Nat) : AspisV8R17.RawReducer.foldBits n = AspisR1BatchedFoldArithmetic.fold n := by
    rw [AspisV8R17.RawReducer.foldBits_eq_fold31]
    rfl
  have h0b' : AspisR1.R22RawQmProductResidues.rawV c d g h ≤
      a*e + (2^31-1)^2-b*f + 2*AspisR1.R22RawQmProductResidues.rawU c d g h + 3*(2^31-1) := by
    unfold AspisR1.R22RawQmProductResidues.rawV AspisR1.R22RawQmProductResidues.rawU
    rw [hfold, hfold]
    simpa [AspisV8R17.RawReducer.P] using h0bFold
  have hprod := AspisR1.R22RawQmProductResidues.raw_coefficients_eq_qmul a b c d e f g h
    hU h0a h0b' h2a h2b
  have hr0 : r.val[0]! = x0 := by rw [hshape]; simp [Array.make]
  have hr1 : r.val[1]! = x1 := by rw [hshape]; simp [Array.make]
  have hr2 : r.val[2]! = x2 := by rw [hshape]; simp [Array.make]
  have hr3 : r.val[3]! = x3 := by rw [hshape]; simp [Array.make]
  have hp0 := congrArg Prod.fst hprod
  have hp1 := congrArg (fun z : M×M×M×M => z.2.1) hprod
  have hp2 := congrArg (fun z : M×M×M×M => z.2.2.1) hprod
  have hp3 := congrArg (fun z : M×M×M×M => z.2.2.2) hprod
  change ((AspisR1.R22RawQmProductResidues.rawC0 a b c d e f g h : Nat) : M) = _ at hp0
  change ((AspisR1.R22RawQmProductResidues.rawC1 a b c d e f g h : Nat) : M) = _ at hp1
  change ((AspisR1.R22RawQmProductResidues.rawC2 a b c d e f g h : Nat) : M) = _ at hp2
  change ((AspisR1.R22RawQmProductResidues.rawC3 a b c d e f g h : Nat) : M) = _ at hp3
  apply Prod.ext
  · calc
      ((r.val[0]!).val : M) = (x0.val : M)  := congrArg (fun x : U64 => (x.val : M)) hr0
      _ = (AspisR1.R22RawQmProductResidues.rawC0 a b c d e f g h : M) := congrArg (fun n : Nat => (n : M)) h0
      _ = _ := hp0
  · apply Prod.ext
    · calc
        ((r.val[1]!).val : M) = (x1.val : M)  := congrArg (fun x : U64 => (x.val : M)) hr1
        _ = (AspisR1.R22RawQmProductResidues.rawC1 a b c d e f g h : M) := congrArg (fun n : Nat => (n : M)) h1
        _ = _ := hp1
    · apply Prod.ext
      · calc
          ((r.val[2]!).val : M) = (x2.val : M)  := congrArg (fun x : U64 => (x.val : M)) hr2
          _ = (AspisR1.R22RawQmProductResidues.rawC2 a b c d e f g h : M) := congrArg (fun n : Nat => (n : M)) h2
          _ = _ := hp2
      · calc
          ((r.val[3]!).val : M) = (x3.val : M)  := congrArg (fun x : U64 => (x.val : M)) hr3
          _ = (AspisR1.R22RawQmProductResidues.rawC3 a b c d e f g h : M) := congrArg (fun n : Nat => (n : M)) h3
          _ = _ := hp3

def castSums (s : Array U64 4#usize) : M × M × M × M :=
  ((s.val[0]!.val : M), ((s.val[1]!.val : M),
    ((s.val[2]!.val : M), (s.val[3]!.val : M))))

def tupleAdd (x y : M × M × M × M) : M × M × M × M :=
  (x.1 + y.1, (x.2.1 + y.2.1,
    (x.2.2.1 + y.2.2.1, x.2.2.2 + y.2.2.2)))

private theorem castSums_updated (s r : Array U64 4#usize)
    (hs : ∀ x ∈ s.val, x.val < 2^46) :
    castSums (AspisR1DotPushLocal.Proof.updatedSums s r) =
      tupleAdd (castSums s) (castSums r) := by
  apply Prod.ext
  · simpa [castSums, tupleAdd] using
      updated_sum_cast_update s r hs 0 (by decide)
  · apply Prod.ext
    · simpa [castSums, tupleAdd] using
        updated_sum_cast_update s r hs 1 (by decide)
    · apply Prod.ext
      · simpa [castSums, tupleAdd] using
          updated_sum_cast_update s r hs 2 (by decide)
      · simpa [castSums, tupleAdd] using
          updated_sum_cast_update s r hs 3 (by decide)

/-- For one successful checked E-by-K push, both actual Dot states advance by
one Q multiplication in the R22 residue field. The canonical input bound is
provided by the selected value caller; accumulator words retain the separate
`< 2^46` invariant required by the source-shaped Dot update. -/
theorem successful_push_decoded_product_update
    (self : PushState) (value : PushWide) (scalar : PushQm) (out : PushState)
    (hcanonical : AspisR1EbyKPowerValueCanonicalToPush.pushCanonical value)
    (hacc0 : ∀ x ∈ self.c0.sums.val, x.val < 2^46)
    (hacc1 : ∀ x ∈ self.c1.sums.val, x.val < 2^46)
    (hrun : AspisR1EbyKPushDotBackend.pushWithDotBackend QRaw self value scalar =
      .ok (.Ok (),out)) :
    castSums out.c0.sums = tupleAdd (castSums self.c0.sums)
      (AspisR1.R22RawQmProductResidues.qmulCoefficients
        ((value.c0.c0.a.val,value.c0.c0.b.val),
         (value.c0.c1.a.val,value.c0.c1.b.val))
        ((scalar.c0.a.val,scalar.c0.b.val),(scalar.c1.a.val,scalar.c1.b.val))) ∧
    castSums out.c1.sums = tupleAdd (castSums self.c1.sums)
      (AspisR1.R22RawQmProductResidues.qmulCoefficients
        ((value.c1.c0.a.val,value.c1.c0.b.val),
         (value.c1.c1.a.val,value.c1.c1.b.val))
        ((scalar.c0.a.val,scalar.c0.b.val),(scalar.c1.a.val,scalar.c1.b.val))) := by
  have hcoeff := AspisR1EbyKPushActualRawCoefficientBounds.successful_push_qraw_coefficients_of_canonical self value scalar out hcanonical hrun
  obtain ⟨lo,hi,hlo,hhi,hloC,hhiC⟩ := hcoeff
  obtain ⟨a,b,c,d,e,f,g,h,x0,x1,x2,x3,hshape,h0,h1,h2,h3,ha,hb,hc,hd,he,hf,hg,hh⟩ := hloC
  obtain ⟨a',b',c',d',e',f',g',h',y0,y1,y2,y3,hshape',h0',h1',h2',h3',ha',hb',hc',hd',he',hf',hg',hh'⟩ := hhiC
  obtain ⟨loB,hiB,hloB,hhiB,hstate0B,hstate1B,hcount,hincrement,hscalar⟩ :=
    AspisR1EbyKPushDotBackend.successful_push_exact_backend QRaw self value scalar out hrun
  have hloEq : loB = lo := Result.ok.inj (hloB.symm.trans hlo)
  have hhiEq : hiB = hi := Result.ok.inj (hhiB.symm.trans hhi)
  have hstate0 : out.c0.sums = AspisR1DotPushLocal.Proof.updatedSums self.c0.sums lo := by
    rw [hloEq] at hstate0B
    exact hstate0B
  have hstate1 : out.c1.sums = AspisR1DotPushLocal.Proof.updatedSums self.c1.sums hi := by
    rw [hhiEq] at hstate1B
    exact hstate1B
  have hv := AspisR1EbyKPowerValueCanonicalToPush.canonical_push_limb_bounds value hcanonical
  have haB : a ≤ 2^31-2 := by rw [ha]; exact hv.1
  have hbB : b ≤ 2^31-2 := by rw [hb]; exact hv.2.1
  have hcB : c ≤ 2^31-2 := by rw [hc]; exact hv.2.2.1
  have hdB : d ≤ 2^31-2 := by rw [hd]; exact hv.2.2.2.1
  have ha'B : a' ≤ 2^31-2 := by rw [ha']; exact hv.2.2.2.2.1
  have hb'B : b' ≤ 2^31-2 := by rw [hb']; exact hv.2.2.2.2.2.1
  have hc'B : c' ≤ 2^31-2 := by rw [hc']; exact hv.2.2.2.2.2.2.1
  have hd'B : d' ≤ 2^31-2 := by rw [hd']; exact hv.2.2.2.2.2.2.2
  have heB : e ≤ 2^31-2 := by rw [he]; have q := hscalar scalar.c0.a (by simp [AspisR1EbyKPushDotBackend.scalarQ, Array.make]); omega
  have hfB : f ≤ 2^31-2 := by rw [hf]; have q := hscalar scalar.c0.b (by simp [AspisR1EbyKPushDotBackend.scalarQ, Array.make]); omega
  have hgB : g ≤ 2^31-2 := by rw [hg]; have q := hscalar scalar.c1.a (by simp [AspisR1EbyKPushDotBackend.scalarQ, Array.make]); omega
  have hhB : h ≤ 2^31-2 := by rw [hh]; have q := hscalar scalar.c1.b (by simp [AspisR1EbyKPushDotBackend.scalarQ, Array.make]); omega
  have he'B : e' ≤ 2^31-2 := by rw [he']; have q := hscalar scalar.c0.a (by simp [AspisR1EbyKPushDotBackend.scalarQ, Array.make]); omega
  have hf'B : f' ≤ 2^31-2 := by rw [hf']; have q := hscalar scalar.c0.b (by simp [AspisR1EbyKPushDotBackend.scalarQ, Array.make]); omega
  have hg'B : g' ≤ 2^31-2 := by rw [hg']; have q := hscalar scalar.c1.a (by simp [AspisR1EbyKPushDotBackend.scalarQ, Array.make]); omega
  have hh'B : h' ≤ 2^31-2 := by rw [hh']; have q := hscalar scalar.c1.b (by simp [AspisR1EbyKPushDotBackend.scalarQ, Array.make]); omega
  have hlow := raw_array_cast_qmul lo a b c d e f g h x0 x1 x2 x3 hshape h0 h1 h2 h3 haB hbB hcB hdB heB hfB hgB hhB
  have hhigh := raw_array_cast_qmul hi a' b' c' d' e' f' g' h' y0 y1 y2 y3 hshape' h0' h1' h2' h3' ha'B hb'B hc'B hd'B he'B hf'B hg'B hh'B
  change castSums lo = _ at hlow
  change castSums hi = _ at hhigh
  constructor
  · calc
      castSums out.c0.sums = castSums (AspisR1DotPushLocal.Proof.updatedSums self.c0.sums lo) := by rw [hstate0]
      _ = tupleAdd (castSums self.c0.sums) (castSums lo) := castSums_updated self.c0.sums lo hacc0
      _ = tupleAdd (castSums self.c0.sums) (AspisR1.R22RawQmProductResidues.qmulCoefficients ((a,b),(c,d)) ((e,f),(g,h))) := by rw [hlow]
      _ = tupleAdd (castSums self.c0.sums) (AspisR1.R22RawQmProductResidues.qmulCoefficients ((value.c0.c0.a.val,value.c0.c0.b.val),(value.c0.c1.a.val,value.c0.c1.b.val)) ((scalar.c0.a.val,scalar.c0.b.val),(scalar.c1.a.val,scalar.c1.b.val))) := by rw [ha,hb,hc,hd,he,hf,hg,hh]
  · calc
      castSums out.c1.sums = castSums (AspisR1DotPushLocal.Proof.updatedSums self.c1.sums hi) := by rw [hstate1]
      _ = tupleAdd (castSums self.c1.sums) (castSums hi) := castSums_updated self.c1.sums hi hacc1
      _ = tupleAdd (castSums self.c1.sums) (AspisR1.R22RawQmProductResidues.qmulCoefficients ((a',b'),(c',d')) ((e',f'),(g',h'))) := by rw [hhigh]
      _ = tupleAdd (castSums self.c1.sums) (AspisR1.R22RawQmProductResidues.qmulCoefficients ((value.c1.c0.a.val,value.c1.c0.b.val),(value.c1.c1.a.val,value.c1.c1.b.val)) ((scalar.c0.a.val,scalar.c0.b.val),(scalar.c1.a.val,scalar.c1.b.val))) := by rw [ha',hb',hc',hd',he',hf',hg',hh']

#print axioms successful_push_decoded_product_update

