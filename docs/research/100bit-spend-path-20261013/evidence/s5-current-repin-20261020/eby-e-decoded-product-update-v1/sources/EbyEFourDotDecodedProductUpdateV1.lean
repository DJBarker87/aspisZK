import AspisR1EbyEFourDotSourceCountConsumerV1
import S5QRaw.EbyKPushDecodedProductUpdateV1
import AspisR1FinishDotReturnedFieldProductV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1EbyEFourDotDecodedProductUpdateV1

open AspisR1EbyEFourDotSourceStepV1
open AspisR1EbyEFourDotFromWideBridgeV1
open AspisR1EbyEFourDotGeneratedPushPortV1
open AspisR1EbyKPushDecodedProductUpdate

abbrev M := AspisR1.R22RawQmProductResidues.M
abbrev Residues := M × M × M × M
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev WideTower := AspisWideTower.WideExact

/-- The coordinate tuple represented by a source M31 pair. -/
def sourceQMResidues (x : AspisR1EbyEDotCutV1.field.QM31) : Residues :=
  ((x.c0.a.val : M), ((x.c0.b.val : M),
    ((x.c1.a.val : M), (x.c1.b.val : M))))

def sourceQResidues (x : AspisR1EbyEFourDotSourceStepV1.Q) : Residues :=
  ((x.val[0]!.val : M), ((x.val[1]!.val : M),
    ((x.val[2]!.val : M), (x.val[3]!.val : M))))

def qRawInput (x : AspisR1EbyKPushDotBackend.PushQ) :
    AspisV8R17.QM31WordResidues.Q :=
  ((x.val[0]!.val, x.val[1]!.val), (x.val[2]!.val, x.val[3]!.val))

def qRawCanonical (x : AspisR1EbyKPushDotBackend.PushQ) : Prop :=
  x.val[0]!.val ≤ 2^31-2 ∧ x.val[1]!.val ≤ 2^31-2 ∧
  x.val[2]!.val ≤ 2^31-2 ∧ x.val[3]!.val ≤ 2^31-2

def decodeResidues (x : Residues) : ExactQM :=
  ⟨⟨x.1, x.2.1⟩, ⟨x.2.2.1, x.2.2.2⟩⟩

def decodeSourceQM (x : AspisR1EbyEDotCutV1.field.QM31) :
    ExactQM := decodeResidues (sourceQMResidues x)

def residuesOfQ (x : AspisV8R17.QM31WordResidues.Q) : Residues :=
  (x.1.1, (x.1.2, (x.2.1, x.2.2)))

def sourceWideDecode (x : Wide) : WideTower :=
  ⟨decodeSourceQM x.c0, decodeSourceQM x.c1⟩

def castSums (s : Array U64 4#usize) : Residues :=
  ((s.val[0]!.val : M), ((s.val[1]!.val : M),
    ((s.val[2]!.val : M), (s.val[3]!.val : M))))

def tupleAdd (x y : Residues) : Residues :=
  (x.1 + y.1, (x.2.1 + y.2.1,
    (x.2.2.1 + y.2.2.1, x.2.2.2 + y.2.2.2)))

def decodeState (s : State) : WideTower :=
  ⟨decodeResidues (castSums s.ac.sums) +
      AspisWideTower.wideU * decodeResidues (castSums s.bd.sums),
   decodeResidues (castSums s.ad.sums) + decodeResidues (castSums s.bc.sums)⟩

def sourceCanonical (x : Wide) : Prop :=
  x.c0.c0.a.val ≤ 2^31-2 ∧ x.c0.c0.b.val ≤ 2^31-2 ∧
  x.c0.c1.a.val ≤ 2^31-2 ∧ x.c0.c1.b.val ≤ 2^31-2 ∧
  x.c1.c0.a.val ≤ 2^31-2 ∧ x.c1.c0.b.val ≤ 2^31-2 ∧
  x.c1.c1.a.val ≤ 2^31-2 ∧ x.c1.c1.b.val ≤ 2^31-2

def sourceLowQ (x : Wide) : AspisR1EbyKPushDotBackend.PushQ :=
  Array.make 4#usize [x.c0.c0.a,x.c0.c0.b,x.c0.c1.a,x.c0.c1.b]

def sourceHighQ (x : Wide) : AspisR1EbyKPushDotBackend.PushQ :=
  Array.make 4#usize [x.c1.c0.a,x.c1.c0.b,x.c1.c1.a,x.c1.c1.b]

private theorem sourceLowQ_canonical (x : Wide) (h : sourceCanonical x) :
    qRawCanonical (sourceLowQ x) := by
  rcases h with ⟨h00,h01,h02,h03,h10,h11,h12,h13⟩
  simpa [qRawCanonical,sourceLowQ,Array.make] using ⟨h00,h01,h02,h03⟩

private theorem sourceHighQ_canonical (x : Wide) (h : sourceCanonical x) :
    qRawCanonical (sourceHighQ x) := by
  rcases h with ⟨h00,h01,h02,h03,h10,h11,h12,h13⟩
  simpa [qRawCanonical,sourceHighQ,Array.make] using ⟨h10,h11,h12,h13⟩

private theorem sourceLowQ_residues (x : Wide) :
    residuesOfQ (qRawInput (sourceLowQ x)) = sourceQMResidues x.c0 := by
  simp [residuesOfQ,qRawInput,sourceLowQ,sourceQMResidues,Array.make]

private theorem sourceHighQ_residues (x : Wide) :
    residuesOfQ (qRawInput (sourceHighQ x)) = sourceQMResidues x.c1 := by
  simp [residuesOfQ,qRawInput,sourceHighQ,sourceQMResidues,Array.make]

theorem sourceFromWide_explicit (x : Wide) :
    AspisR1EbyEFourDotFromWideBridgeV1.sourceFromWide x =
      .ok (Array.make 2#usize [sourceLowQ x,sourceHighQ x]) := by
  simp [AspisR1EbyEFourDotFromWideBridgeV1.sourceFromWide,
    AspisR1EbyEFourDotFromWideBridgeV1.sourceToLimbs,sourceLowQ,sourceHighQ,
    Array.index_usize,Array.make]

private theorem sourceFromWide_success_parts
    (x : Wide) (parts : Array AspisR1EbyEFourDotSourceStepV1.Q 2#usize)
    (h : AspisR1EbyEFourDotFromWideBridgeV1.sourceFromWide x = .ok parts) :
    parts = Array.make 2#usize [sourceLowQ x,sourceHighQ x] := by
  exact Result.ok.inj (h.symm.trans (sourceFromWide_explicit x))

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

private theorem castSums_updated (s r : Array U64 4#usize)
    (hs : ∀ x ∈ s.val, x.val < 2^46) :
    castSums (AspisR1DotPushLocal.Proof.updatedSums s r) =
      tupleAdd (castSums s) (castSums r) := by
  apply Prod.ext
  · simpa [castSums, tupleAdd] using updated_sum_cast_update s r hs 0 (by decide)
  · apply Prod.ext
    · simpa [castSums, tupleAdd] using updated_sum_cast_update s r hs 1 (by decide)
    · apply Prod.ext
      · simpa [castSums, tupleAdd] using updated_sum_cast_update s r hs 2 (by decide)
      · simpa [castSums, tupleAdd] using updated_sum_cast_update s r hs 3 (by decide)


private theorem tupleToTowerQ_add (x y : Residues) :
    decodeResidues (tupleAdd x y) = decodeResidues x + decodeResidues y := by
  ext <;> simp [decodeResidues, tupleAdd]

/-- Decoding the four Q products used by EbyEDot gives multiplication in the
outer quadratic field, with the deployed relation v² = u. -/
theorem outer_quadratic_mul (a b c d : ExactQM) :
    (⟨a*c + AspisWideTower.wideU * b*d, a*d+b*c⟩ : WideTower) =
      (⟨a,b⟩ : WideTower) * ⟨c,d⟩ := by
  apply QuadraticAlgebra.ext
  · simp only [QuadraticAlgebra.re_mul]
    <;> ring
  · simp only [QuadraticAlgebra.im_mul]
    <;> ring

theorem tupleToTowerQ_qmul_mul (x y : AspisV8R17.QM31WordResidues.Q) :
    decodeResidues (AspisR1.R22RawQmProductResidues.qmulCoefficients x y) =
      decodeResidues (residuesOfQ x) * decodeResidues (residuesOfQ y) := by
  calc
    _ = AspisR1FinishDotReturnedDeltaDecodeV1.tupleToTowerQ
        (AspisR1.R22RawQmProductResidues.qmulCoefficients x y) := by
          rfl
    _ = AspisV8R17.QM31WordTower.embedQ
        (AspisV8R17.QM31WordResidues.qMul x y) :=
          AspisR1FinishDotReturnedFieldProductV1.tupleToTowerQ_qmul x y
    _ = AspisV8R17.QM31WordTower.embedQ x * AspisV8R17.QM31WordTower.embedQ y := by
          rw [AspisV8R17.QM31WordTower.embed_product,
            AspisV8R17.QuadraticTowerOperations.qmul_eq]
    _ = decodeResidues (residuesOfQ x) * decodeResidues (residuesOfQ y) := by
          rfl

private theorem sourceLow_product (x y : Wide) :
    decodeResidues (AspisR1.R22RawQmProductResidues.qmulCoefficients
      (qRawInput (sourceLowQ x)) (qRawInput (sourceLowQ y))) =
      decodeSourceQM x.c0 * decodeSourceQM y.c0 := by
  rw [tupleToTowerQ_qmul_mul,sourceLowQ_residues,sourceLowQ_residues]
  rfl

private theorem sourceHigh_product (x y : Wide) :
    decodeResidues (AspisR1.R22RawQmProductResidues.qmulCoefficients
      (qRawInput (sourceHighQ x)) (qRawInput (sourceHighQ y))) =
      decodeSourceQM x.c1 * decodeSourceQM y.c1 := by
  rw [tupleToTowerQ_qmul_mul,sourceHighQ_residues,sourceHighQ_residues]
  rfl

private theorem sourceLowHigh_product (x y : Wide) :
    decodeResidues (AspisR1.R22RawQmProductResidues.qmulCoefficients
      (qRawInput (sourceLowQ x)) (qRawInput (sourceHighQ y))) =
      decodeSourceQM x.c0 * decodeSourceQM y.c1 := by
  rw [tupleToTowerQ_qmul_mul,sourceLowQ_residues,sourceHighQ_residues]
  rfl

private theorem sourceHighLow_product (x y : Wide) :
    decodeResidues (AspisR1.R22RawQmProductResidues.qmulCoefficients
      (qRawInput (sourceHighQ x)) (qRawInput (sourceLowQ y))) =
      decodeSourceQM x.c1 * decodeSourceQM y.c0 := by
  rw [tupleToTowerQ_qmul_mul,sourceHighQ_residues,sourceLowQ_residues]
  rfl


private theorem bind_ok_inv_local {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) : ∃ y, r = .ok y ∧ f y = .ok x := by
  cases r with
  | ok y => exact ⟨y,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

private theorem foldBits_fold (n : Nat) :
    AspisV8R17.RawReducer.foldBits n = AspisR1BatchedFoldArithmetic.fold n := by
  rw [AspisV8R17.RawReducer.foldBits_eq_fold31]
  rfl

private theorem indexed_bound_to_members (s : Array U64 4#usize)
    (h : ∀ j, ∀ hj : j < 4, (s.val[j]'(by rw [s.property]; exact hj)).val < 2^46) :
    ∀ x ∈ s.val, x.val < 2^46 := by
  intro x hx
  have hmem := List.mem_iff_getElem.mp hx
  rcases hmem with ⟨i, hi, hix⟩
  subst x
  have hi4 : i < 4 := by simpa [s.property] using hi
  exact h i hi4

/-- The selected actual Q.raw result has the R22 QM31 product residues when
all eight source limbs are canonical. -/
theorem raw_decode_qmul_of_success
    (a b : AspisR1EbyKPushDotBackend.PushQ) (out : Array U64 4#usize)
    (ha : qRawCanonical a) (hb : qRawCanonical b)
    (hraw : AspisR1EbyKPushActualRawCoefficientBounds.QRaw a b = .ok out) :
    castSums out = AspisR1.R22RawQmProductResidues.qmulCoefficients
      (qRawInput a) (qRawInput b) := by
  rcases ha with ⟨ha0,ha1,ha2,ha3⟩
  rcases hb with ⟨hb0,hb1,hb2,hb3⟩
  obtain ⟨na,nb,nc,nd,ne,nf,ng,nh,x0,x1,x2,x3,
      hshape,h0,h1,h2,h3,hna,hnb,hnc,hnd,hne,hnf,hng,hnh⟩ :=
    AspisR1QRawActualC0V2.actual_raw_coefficients_of_input_bounds_v2
      a b out hraw ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
  have hguards := AspisR1S5CurrentRepin.canonical_raw_range_guards
    na nb nc nd ne nf ng nh
    (by rw [hna]; exact ha0) (by rw [hnb]; exact ha1)
    (by rw [hnc]; exact ha2) (by rw [hnd]; exact ha3)
    (by rw [hne]; exact hb0) (by rw [hnf]; exact hb1)
    (by rw [hng]; exact hb2) (by rw [hnh]; exact hb3)
  dsimp only at hguards
  rcases hguards with ⟨_,hU,_,_,h0a,_,_,h0bFold,_,_,_,_,_,h2a,h2b,_,_,_,_⟩
  have h0b : AspisR1.R22RawQmProductResidues.rawV nc nd ng nh ≤
      na*ne + (2^31-1)^2 - nb*nf +
        2*AspisR1.R22RawQmProductResidues.rawU nc nd ng nh + 3*(2^31-1) := by
    unfold AspisR1.R22RawQmProductResidues.rawV AspisR1.R22RawQmProductResidues.rawU
    rw [foldBits_fold, foldBits_fold]
    simpa [AspisV8R17.RawReducer.P] using h0bFold
  have hprod := AspisR1.R22RawQmProductResidues.raw_coefficients_eq_qmul
    na nb nc nd ne nf ng nh hU h0a h0b h2a h2b
  have hr0 : out.val[0]! = x0 := by rw [hshape]; simp [Array.make]
  have hr1 : out.val[1]! = x1 := by rw [hshape]; simp [Array.make]
  have hr2 : out.val[2]! = x2 := by rw [hshape]; simp [Array.make]
  have hr3 : out.val[3]! = x3 := by rw [hshape]; simp [Array.make]
  have hp0 := congrArg Prod.fst hprod
  have hp1 := congrArg (fun z : M×M×M×M => z.2.1) hprod
  have hp2 := congrArg (fun z : M×M×M×M => z.2.2.1) hprod
  have hp3 := congrArg (fun z : M×M×M×M => z.2.2.2) hprod
  change ((AspisR1.R22RawQmProductResidues.rawC0 na nb nc nd ne nf ng nh : Nat) : M) = _ at hp0
  change ((AspisR1.R22RawQmProductResidues.rawC1 na nb nc nd ne nf ng nh : Nat) : M) = _ at hp1
  change ((AspisR1.R22RawQmProductResidues.rawC2 na nb nc nd ne nf ng nh : Nat) : M) = _ at hp2
  change ((AspisR1.R22RawQmProductResidues.rawC3 na nb nc nd ne nf ng nh : Nat) : M) = _ at hp3
  have hinputA : (((na : M),(nb : M)),((nc : M),(nd : M))) = qRawInput a := by
    simp [qRawInput,hna,hnb,hnc,hnd]
  have hinputB : (((ne : M),(nf : M)),((ng : M),(nh : M))) = qRawInput b := by
    simp [qRawInput,hne,hnf,hng,hnh]
  rw [hinputA,hinputB] at hp0 hp1 hp2 hp3
  apply Prod.ext
  · calc
      ((out.val[0]!).val : M) = (x0.val : M) := congrArg (fun z : U64 => (z.val : M)) hr0
      _ = (AspisR1.R22RawQmProductResidues.rawC0 na nb nc nd ne nf ng nh : M) :=
        congrArg (fun z : Nat => (z : M)) h0
      _ = _ := hp0
  · apply Prod.ext
    · calc
        ((out.val[1]!).val : M) = (x1.val : M) := congrArg (fun z : U64 => (z.val : M)) hr1
        _ = (AspisR1.R22RawQmProductResidues.rawC1 na nb nc nd ne nf ng nh : M) :=
          congrArg (fun z : Nat => (z : M)) h1
        _ = _ := hp1
    · apply Prod.ext
      · calc
          ((out.val[2]!).val : M) = (x2.val : M) := congrArg (fun z : U64 => (z.val : M)) hr2
          _ = (AspisR1.R22RawQmProductResidues.rawC2 na nb nc nd ne nf ng nh : M) :=
            congrArg (fun z : Nat => (z : M)) h2
          _ = _ := hp2
      · calc
          ((out.val[3]!).val : M) = (x3.val : M) := congrArg (fun z : U64 => (z.val : M)) hr3
          _ = (AspisR1.R22RawQmProductResidues.rawC3 na nb nc nd ne nf ng nh : M) :=
            congrArg (fun z : Nat => (z : M)) h3
          _ = _ := hp3

private theorem decoded_dot_update
    (s r : Array U64 4#usize) (a b : AspisR1EbyKPushDotBackend.PushQ)
    (hs : ∀ x ∈ s.val, x.val < 2^46)
    (ha : qRawCanonical a) (hb : qRawCanonical b)
    (hraw : AspisR1EbyKPushActualRawCoefficientBounds.QRaw a b = .ok r) :
    decodeResidues (castSums (AspisR1DotPushLocal.Proof.updatedSums s r)) =
      decodeResidues (castSums s) +
        decodeResidues (AspisR1.R22RawQmProductResidues.qmulCoefficients
          (qRawInput a) (qRawInput b)) := by
  calc
    _ = decodeResidues (tupleAdd (castSums s) (castSums r)) := by
      rw [castSums_updated s r hs]
    _ = decodeResidues (castSums s) + decodeResidues (castSums r) :=
      tupleToTowerQ_add (castSums s) (castSums r)
    _ = decodeResidues (castSums s) +
        decodeResidues (AspisR1.R22RawQmProductResidues.qmulCoefficients
          (qRawInput a) (qRawInput b)) := by
      rw [raw_decode_qmul_of_success a b r ha hb hraw]
    _ = _ := rfl

/-- One successful generated EbyE push adds the field product of its two
source WideExact operands to the decoded four-Dot accumulator.  The source
canonicality bound supplies the Q.raw input bounds; the count-indexed
accumulator invariant supplies the four pre-accumulator bounds required by
the checked source Dot update. -/
theorem emitted_push_decoded_product_update
    (n : Nat) (self out : State) (left right : Wide)
    (hinv : AspisR1EbyEFourDotSourceStepV1.Bounded n self)
    (hcount : self.count.val = n)
    (hleftCanonical : sourceCanonical left)
    (hrightCanonical : sourceCanonical right)
    (hrun : AspisR1EbyEFourDotGeneratedPushPortV1.emittedPushParameterized
      AspisR1EbyEFourDotSourceStepV1.maxTerms
      AspisR1EbyEFourDotFromWideBridgeV1.sourceFromWide
      (AspisR1EbyEFourDotSourceStepV1.dotViaRawSource
        AspisR1EbyKPushActualRawCoefficientBounds.QRaw)
      AspisR1EbyEFourDotSourceStepV1.sourceAddUsize self left right =
        .ok (.Ok (),out)) :
    decodeState out = decodeState self + sourceWideDecode left * sourceWideDecode right := by
  have hsource : AspisR1EbyEFourDotSourceStepV1.pushWithOps
      AspisR1EbyEFourDotFromWideBridgeV1.sourceFromWide
      (AspisR1EbyEFourDotSourceStepV1.dotViaRawSource
        AspisR1EbyKPushActualRawCoefficientBounds.QRaw)
      AspisR1EbyEFourDotSourceStepV1.sourceAddUsize self left right =
        .ok (.Ok (),out) := by
    have heq := AspisR1EbyEFourDotGeneratedPushPortV1.emittedPushParameterized_eq_sourceSchedule
      AspisR1EbyEFourDotFromWideBridgeV1.sourceFromWide
      (AspisR1EbyEFourDotSourceStepV1.dotViaRawSource
        AspisR1EbyKPushActualRawCoefficientBounds.QRaw)
      AspisR1EbyEFourDotSourceStepV1.sourceAddUsize self left right
    exact heq.symm ▸ hrun
  obtain ⟨_,hpreAC,hpreBD,hpreAD,hpreBC⟩ :=
    AspisR1EbyEFourDotSourceStepV1.successful_four_dot_count_bound
      AspisR1EbyEFourDotFromWideBridgeV1.sourceFromWide
      AspisR1EbyKPushActualRawCoefficientBounds.QRaw n self out left right
      hinv hcount hsource
  obtain ⟨leftParts,rightParts,a,b,c,d,rawAC,rawBD,rawAD,rawBC,i,
      hbelow,hleft,hleft0,hleft1,hright,hright0,hright1,
      hrawAC,hrawBD,hrawAD,hrawBC,hstateAC,hstateBD,hstateAD,hstateBC,
      hadd,houtCount⟩ :=
    AspisR1EbyEFourDotSourceStepV1.push_success_four_dot_raw
      AspisR1EbyEFourDotFromWideBridgeV1.sourceFromWide
      AspisR1EbyKPushActualRawCoefficientBounds.QRaw
      AspisR1EbyEFourDotSourceStepV1.sourceAddUsize self left right out hsource
  have hleftParts := sourceFromWide_success_parts left leftParts hleft
  have hrightParts := sourceFromWide_success_parts right rightParts hright
  rw [hleftParts] at hleft0 hleft1
  rw [hrightParts] at hright0 hright1
  have hleft0' : a = sourceLowQ left := Result.ok.inj
    (hleft0.symm.trans (by simp [Array.index_usize,Array.make]))
  have hleft1' : b = sourceHighQ left := Result.ok.inj
    (hleft1.symm.trans (by simp [Array.index_usize,Array.make]))
  have hright0' : c = sourceLowQ right := Result.ok.inj
    (hright0.symm.trans (by simp [Array.index_usize,Array.make]))
  have hright1' : d = sourceHighQ right := Result.ok.inj
    (hright1.symm.trans (by simp [Array.index_usize,Array.make]))
  have hcanA : qRawCanonical a := by rw [hleft0']; exact sourceLowQ_canonical left hleftCanonical
  have hcanB : qRawCanonical b := by rw [hleft1']; exact sourceHighQ_canonical left hleftCanonical
  have hcanC : qRawCanonical c := by rw [hright0']; exact sourceLowQ_canonical right hrightCanonical
  have hcanD : qRawCanonical d := by rw [hright1']; exact sourceHighQ_canonical right hrightCanonical
  have hpreAC' := indexed_bound_to_members self.ac.sums hpreAC
  have hpreBD' := indexed_bound_to_members self.bd.sums hpreBD
  have hpreAD' := indexed_bound_to_members self.ad.sums hpreAD
  have hpreBC' := indexed_bound_to_members self.bc.sums hpreBC
  have hupdateAC := decoded_dot_update self.ac.sums rawAC a c hpreAC' hcanA hcanC hrawAC
  have hupdateBD := decoded_dot_update self.bd.sums rawBD b d hpreBD' hcanB hcanD hrawBD
  have hupdateAD := decoded_dot_update self.ad.sums rawAD a d hpreAD' hcanA hcanD hrawAD
  have hupdateBC := decoded_dot_update self.bc.sums rawBC b c hpreBC' hcanB hcanC hrawBC
  have hprodAC : decodeResidues (AspisR1.R22RawQmProductResidues.qmulCoefficients
      (qRawInput a) (qRawInput c)) = decodeSourceQM left.c0 * decodeSourceQM right.c0 := by
    rw [hleft0',hright0']; exact sourceLow_product left right
  have hprodBD : decodeResidues (AspisR1.R22RawQmProductResidues.qmulCoefficients
      (qRawInput b) (qRawInput d)) = decodeSourceQM left.c1 * decodeSourceQM right.c1 := by
    rw [hleft1',hright1']; exact sourceHigh_product left right
  have hprodAD : decodeResidues (AspisR1.R22RawQmProductResidues.qmulCoefficients
      (qRawInput a) (qRawInput d)) = decodeSourceQM left.c0 * decodeSourceQM right.c1 := by
    rw [hleft0',hright1']; exact sourceLowHigh_product left right
  have hprodBC : decodeResidues (AspisR1.R22RawQmProductResidues.qmulCoefficients
      (qRawInput b) (qRawInput c)) = decodeSourceQM left.c1 * decodeSourceQM right.c0 := by
    rw [hleft1',hright0']; exact sourceHighLow_product left right
  have hAC : decodeResidues (castSums out.ac.sums) =
      decodeResidues (castSums self.ac.sums) + decodeSourceQM left.c0 * decodeSourceQM right.c0 := by
    calc
      _ = decodeResidues (castSums (AspisR1DotPushLocal.Proof.updatedSums self.ac.sums rawAC)) := by rw [hstateAC]
      _ = decodeResidues (castSums self.ac.sums) + decodeResidues (AspisR1.R22RawQmProductResidues.qmulCoefficients (qRawInput a) (qRawInput c)) := hupdateAC
      _ = _ := by rw [hprodAC]
  have hBD : decodeResidues (castSums out.bd.sums) =
      decodeResidues (castSums self.bd.sums) + decodeSourceQM left.c1 * decodeSourceQM right.c1 := by
    calc
      _ = decodeResidues (castSums (AspisR1DotPushLocal.Proof.updatedSums self.bd.sums rawBD)) := by rw [hstateBD]
      _ = decodeResidues (castSums self.bd.sums) + decodeResidues (AspisR1.R22RawQmProductResidues.qmulCoefficients (qRawInput b) (qRawInput d)) := hupdateBD
      _ = _ := by rw [hprodBD]
  have hAD : decodeResidues (castSums out.ad.sums) =
      decodeResidues (castSums self.ad.sums) + decodeSourceQM left.c0 * decodeSourceQM right.c1 := by
    calc
      _ = decodeResidues (castSums (AspisR1DotPushLocal.Proof.updatedSums self.ad.sums rawAD)) := by rw [hstateAD]
      _ = decodeResidues (castSums self.ad.sums) + decodeResidues (AspisR1.R22RawQmProductResidues.qmulCoefficients (qRawInput a) (qRawInput d)) := hupdateAD
      _ = _ := by rw [hprodAD]
  have hBC : decodeResidues (castSums out.bc.sums) =
      decodeResidues (castSums self.bc.sums) + decodeSourceQM left.c1 * decodeSourceQM right.c0 := by
    calc
      _ = decodeResidues (castSums (AspisR1DotPushLocal.Proof.updatedSums self.bc.sums rawBC)) := by rw [hstateBC]
      _ = decodeResidues (castSums self.bc.sums) + decodeResidues (AspisR1.R22RawQmProductResidues.qmulCoefficients (qRawInput b) (qRawInput c)) := hupdateBC
      _ = _ := by rw [hprodBC]
  change
    (⟨decodeResidues (castSums out.ac.sums) + AspisWideTower.wideU * decodeResidues (castSums out.bd.sums),
       decodeResidues (castSums out.ad.sums) + decodeResidues (castSums out.bc.sums)⟩ : WideTower) = _
  rw [hAC,hBD,hAD,hBC]
  change _ = decodeState self +
    (⟨decodeSourceQM left.c0,decodeSourceQM left.c1⟩ : WideTower) *
      ⟨decodeSourceQM right.c0,decodeSourceQM right.c1⟩
  have hproduct :
      (⟨decodeSourceQM left.c0,decodeSourceQM left.c1⟩ : WideTower) *
        ⟨decodeSourceQM right.c0,decodeSourceQM right.c1⟩ =
      ⟨decodeSourceQM left.c0 * decodeSourceQM right.c0 +
          AspisWideTower.wideU * decodeSourceQM left.c1 * decodeSourceQM right.c1,
        decodeSourceQM left.c0 * decodeSourceQM right.c1 +
          decodeSourceQM left.c1 * decodeSourceQM right.c0⟩ :=
    (outer_quadratic_mul _ _ _ _).symm
  rw [hproduct]
  apply QuadraticAlgebra.ext
  · simp only [QuadraticAlgebra.re_add, decodeState]
    <;> ring
  · simp only [QuadraticAlgebra.im_add, decodeState]
    <;> ring


end AspisR1EbyEFourDotDecodedProductUpdateV1

#print axioms AspisR1EbyEFourDotDecodedProductUpdateV1.emitted_push_decoded_product_update
