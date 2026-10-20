import CurrentClaimScalarChain
import CurrentClaimScalarReads
import CurrentClaimParserInstance
import ClaimDotConcreteAdapterV1
import FinishDotCountBoundV3
import S5QRaw.EbyKPushDecodedProductUpdateV1
import EbyKPushDotBackend
import EbyKPowerValueCanonicalToPushV5
import AspisR1S5ClaimScalarFinishCanonical
import AspisR1FinishDotReturnedDeltaDecodeV1
import AspisR1FinishDotReturnedFieldProductV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S5ClaimScalarConcreteQRawTrace

open AspisR1CurrentPreparedClaim
open AspisR1CurrentPreparedClaim.ClaimScalar
open AspisR1S5ClaimDotConcreteAdapter
open AspisR1FinishDotCountBoundV2
open AspisR1EbyKPushDecodedProductUpdate

theorem finishFromPush_decode_state_delta (s : AspisR1EbyKPushDotBackend.PushState)
    (f : AspisR1FinishDotDecodedProductTrace.FinishE)
    (hf : AspisR1FinishDotSourceABI.finishFromPush s = .ok f) :
    AspisR1CurrentWide.Proof.decodeFinish f =
      AspisR1FinishDotReturnedDeltaDecodeV1.decodeDelta
        (AspisR1FinishDotDecodedProductTrace.stateDelta s) := by
  cases s with
  | mk c0 c1 count =>
    cases c0 with
    | mk s0 =>
      cases c1 with
      | mk s1 =>
        obtain ⟨a,b,c,d,hshape0⟩ := List.length_eq_four.mp s0.property
        obtain ⟨e,f0,g,h,hshape1⟩ := List.length_eq_four.mp s1.property
        have hwords := AspisR1FinishDotSourceABI.finishFromPush_success_canonical
          ⟨⟨s0⟩,⟨s1⟩,count⟩ f hf
        have hvals := congrArg (List.map (fun w : U32 => w.val)) hwords.2
        rw [hshape0,hshape1] at hvals
        simp only [AspisR1FinishDotSourceABI.finishWords,
          List.map_map,Function.comp_def,List.map_append,List.map_cons,List.map_nil,
          AspisR1EbyKFinish.Proof.word,
          AspisR1CanonicalDotFinish.Proof.canonicalWord_val,
          List.append_nil] at hvals
        injection hvals with ha htail0
        injection htail0 with hb htail1
        injection htail1 with hc htail2
        injection htail2 with hd htail3
        injection htail3 with he htail4
        injection htail4 with hf0 htail5
        injection htail5 with hg htail6
        injection htail6 with hh htail7
        have hlow :
            AspisV8R17.QM31WordTower.decodeQ
                (AspisR1FinishDotReturnedProductWords.finishQMWords f.c0) =
              AspisR1FinishDotReturnedDeltaDecodeV1.tupleToTowerQ
                (AspisR1EbyKPushDecodedProductUpdate.castSums s0) := by
          simp [AspisR1FinishDotReturnedProductWords.finishQMWords,
            AspisR1FinishDotReturnedDeltaDecodeV1.tupleToTowerQ,
            AspisR1EbyKPushDecodedProductUpdate.castSums,
            hshape0,ha,hb,hc,hd,AspisV8R17.QM31WordTower.decodeQ,
            AspisV8R17.QM31WordTower.decodeC,AspisV8R17.QM31WordTower.embedQ,
            AspisV8R17.QM31WordTower.embedC,AspisV8R17.QM31WordResidues.decodeQ,
            AspisV8R17.QM31WordResidues.decodeC,ZMod.natCast_mod]
        have hhigh :
            AspisV8R17.QM31WordTower.decodeQ
                (AspisR1FinishDotReturnedProductWords.finishQMWords f.c1) =
              AspisR1FinishDotReturnedDeltaDecodeV1.tupleToTowerQ
                (AspisR1EbyKPushDecodedProductUpdate.castSums s1) := by
          simp [AspisR1FinishDotReturnedProductWords.finishQMWords,
            AspisR1FinishDotReturnedDeltaDecodeV1.tupleToTowerQ,
            AspisR1EbyKPushDecodedProductUpdate.castSums,
            hshape1,he,hf0,hg,hh,AspisV8R17.QM31WordTower.decodeQ,
            AspisV8R17.QM31WordTower.decodeC,AspisV8R17.QM31WordTower.embedQ,
            AspisV8R17.QM31WordTower.embedC,AspisV8R17.QM31WordResidues.decodeQ,
            AspisV8R17.QM31WordResidues.decodeC,ZMod.natCast_mod]
        have hdecode := AspisR1FinishDotReturnedDecodedValueV1.decodeFinish_eq_word_tower f
        rw [hdecode]
        simp [AspisR1FinishDotReturnedDeltaDecodeV1.decodeDelta,
          AspisR1FinishDotDecodedProductTrace.stateDelta,hlow,hhigh]

abbrev M := AspisR1.R22RawQmProductResidues.M
abbrev PushState := AspisR1EbyKPushDotBackend.PushState
abbrev ClaimWide := Concrete.E
abbrev ClaimQM := aspis_core.field.QM31
abbrev Delta := (M × M × M × M) × (M × M × M × M)

def stateDelta (s : PushState) : Delta :=
  (castSums s.c0.sums, castSums s.c1.sums)

def deltaAdd (x y : Delta) : Delta :=
  (tupleAdd x.1 y.1, tupleAdd x.2 y.2)

def queryDelta (x : ClaimWide) (q : ClaimQM) : Delta :=
  (AspisR1.R22RawQmProductResidues.qmulCoefficients
    ((x.c0.c0.a.val,x.c0.c0.b.val),(x.c0.c1.a.val,x.c0.c1.b.val))
    ((q.c0.a.val,q.c0.b.val),(q.c1.a.val,q.c1.b.val)),
   AspisR1.R22RawQmProductResidues.qmulCoefficients
    ((x.c1.c0.a.val,x.c1.c0.b.val),(x.c1.c1.a.val,x.c1.c1.b.val))
    ((q.c0.a.val,q.c0.b.val),(q.c1.a.val,q.c1.b.val)))

def deltaSum : List (Usize × ClaimWide × ClaimQM) → Delta
  | [] => (0,0)
  | t::xs => deltaAdd (queryDelta t.2.1 t.2.2) (deltaSum xs)

def claimToFinishE (x : ClaimWide) : AspisR1FinishDotDecodedProductTrace.FinishE :=
  AspisR1CurrentWide.Proof.toFinishE (Concrete.toFull x)

def claimToFinishQM (q : ClaimQM) : AspisR1FinishDotDecodedProductTrace.FinishQM :=
  AspisR1CurrentWide.Proof.toFinishQM (Concrete.toQM q)

def finishRows (xs : List (Usize × ClaimWide × ClaimQM)) :
    List (Usize × AspisR1FinishDotDecodedProductTrace.FinishE ×
      AspisR1FinishDotDecodedProductTrace.FinishQM) :=
  xs.map (fun t => (t.1, claimToFinishE t.2.1, claimToFinishQM t.2.2))

theorem deltaSum_finishRows (xs : List (Usize × ClaimWide × ClaimQM)) :
    deltaSum xs = AspisR1FinishDotDecodedProductTrace.deltaSum (finishRows xs) := by
  induction xs with
  | nil => rfl
  | cons t xs ih =>
    rcases t with ⟨index, coeff, scalar⟩
    simp only [deltaSum, finishRows, List.map_cons,
      AspisR1FinishDotDecodedProductTrace.deltaSum]
    rw [ih]
    rfl

def countInv (j : Nat) (s : PushState) : Prop :=
  sumsBelowCount j s.c0.sums ∧ sumsBelowCount j s.c1.sums ∧ s.count.val = j

theorem chain_qraw_delta_trace {H : Type}
    (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (g : Array ClaimWide 29#usize) (point : Usize)
    {iter : AspisR1CurrentPreparedClaim.Range} {initial : PushState} {out : ClaimWide}
    (hweightCanonical : ∀ i x, Array.index_usize g i = .ok x → Concrete.Canonical x)
    (hinv : countInv iter.start.val initial)
    (trace : Chain (concreteOps AspisR1EbyKPushDecodedProductUpdate.QRaw)
      sem y1 g point iter initial out) :
    ∃ final : PushState, ∃ xs : List (Usize × ClaimWide × ClaimQM),
      stateDelta final = deltaAdd (stateDelta initial) (deltaSum xs) ∧
      countInv 29 final ∧
      Concrete.Canonical out ∧
      (concreteOps AspisR1EbyKPushDecodedProductUpdate.QRaw).finishDot final = .ok out ∧
      xs.length + iter.start.val = 29 ∧
      (∀ k, ∀ hk : k < xs.length, (xs[k]'hk).1.val = iter.start.val + k) ∧
      (∀ t ∈ xs, read (concreteOps AspisR1EbyKPushDecodedProductUpdate.QRaw)
          sem y1 point t.1 = .ok t.2.2 ∧
        Array.index_usize g t.1 = .ok t.2.1) := by
  induction trace with
  | done r d x hend hfinish =>
      have hinv' : countInv 29 d := by
        have hs : r.start.val = 29 := hend
        rw [← hs]
        exact hinv
      refine ⟨d, [], ?_, hinv', AspisR1S5ClaimScalarFinishCanonical.concrete_finishDot_success_canonical
          d AspisR1EbyKPushDecodedProductUpdate.QRaw x hfinish,
        hfinish, ?_, ?_, ?_⟩
      · simp [stateDelta, deltaAdd, tupleAdd, deltaSum]
      · simp [hend]
      · intro k hk
        simp at hk
      · intro t ht
        simp at ht
  | @step r r' d d' x l coeff scalar hnext hread hweight hpush tail ih =>
      obtain ⟨hl,hactive,hstart,hend'⟩ := ClaimTrace.next_some_step r r' l hnext
      have hpush' : AspisR1EbyKPushDotBackend.pushWithDotBackend
          AspisR1EbyKPushDecodedProductUpdate.QRaw d (toPushWide coeff) (toPushQm scalar) =
          .ok (.Ok (),d') := by
        simpa only [concreteOps_pushDot] using hpush
      obtain ⟨lo,hi,hlo,hhi,hstate0,hstate1,hguard,hcount,hscalar⟩ :=
        AspisR1EbyKPushDotBackend.successful_push_exact_backend
          AspisR1EbyKPushDecodedProductUpdate.QRaw d (toPushWide coeff) (toPushQm scalar) d' hpush'
      have hguardNat : r.start.val < 4096 := by
        have hc : d.count.val < 4096 := by
          simpa [AspisR1EbyKPushExplicitOpsV1.maxTerms] using hguard
        have heq : d.count.val = r.start.val := hinv.2.2
        omega
      have hinv0 : sumsBelowCount d.count.val d.c0.sums := by
        simpa [hinv.2.2] using hinv.1
      have hinv1 : sumsBelowCount d.count.val d.c1.sums := by
        simpa [hinv.2.2] using hinv.2.1
      have hacc0 : ∀ x ∈ d.c0.sums.val, x.val < 2^46 := by
        intro x hx
        have hex := List.mem_iff_getElem.mp hx
        rcases hex with ⟨i,hi,hix⟩
        subst x
        have hi4 : i < 4 := by simpa [d.c0.sums.property] using hi
        have h := count_bound_to_preaccumulator d.count.val d.c0.sums
          (by simpa [AspisR1EbyKPushExplicitOpsV1.maxTerms] using hguard) hinv0 i hi4
        exact h
      have hacc1 : ∀ x ∈ d.c1.sums.val, x.val < 2^46 := by
        intro x hx
        have hex := List.mem_iff_getElem.mp hx
        rcases hex with ⟨i,hi,hix⟩
        subst x
        have hi4 : i < 4 := by simpa [d.c1.sums.property] using hi
        have h := count_bound_to_preaccumulator d.count.val d.c1.sums
          (by simpa [AspisR1EbyKPushExplicitOpsV1.maxTerms] using hguard) hinv1 i hi4
        exact h
      have hcanonical : AspisR1EbyKPowerValueCanonicalToPush.pushCanonical (toPushWide coeff) := by
        have hb := hweightCanonical l coeff hweight
        change AspisR1CurrentWide.Proof.CanonicalWide (Concrete.toFull coeff) at hb
        change AspisR1CurrentWideMul.CanonicalWide
          (AspisR1EbyKPowerValueCanonicalToPush.pushToSource (toPushWide coeff))
        simp [Concrete.toFull, Concrete.toQM, Concrete.toCM,
          AspisR1EbyKPowerValueCanonicalToPush.pushToSource,
          toPushWide, toPushQm,
          AspisR1CurrentWideMul.CanonicalWide, AspisR1CurrentWideMul.CanonicalQM,
          AspisR1CurrentWide.Proof.CanonicalWide, AspisR1CurrentWide.Proof.CanonicalQM,
          AspisR1CurrentWide.Proof.toQM, AspisR1CurrentWide.Proof.toCM] at hb ⊢
        exact hb
      have hupdate := successful_push_decoded_product_update d (toPushWide coeff)
        (toPushQm scalar) d' hcanonical hacc0 hacc1 hpush'
      have hpost0 : sumsBelowCount d'.count.val d'.c0.sums :=
        (successful_push_preserves_count_bound
          AspisR1EbyKPushDecodedProductUpdate.QRaw d (toPushWide coeff)
          (toPushQm scalar) d' hinv0 hinv1 hpush').1
      have hpost1 : sumsBelowCount d'.count.val d'.c1.sums :=
        (successful_push_preserves_count_bound
          AspisR1EbyKPushDecodedProductUpdate.QRaw d (toPushWide coeff)
          (toPushQm scalar) d' hinv0 hinv1 hpush').2.1
      have hidx : r'.start.val = r.start.val + 1 := hstart
      have hcount' : d'.count.val = r'.start.val := by
        calc
          d'.count.val = d.count.val + 1 := hcount
          _ = r.start.val + 1 := by rw [hinv.2.2]
          _ = r'.start.val := hidx.symm
      have hinv' : countInv r'.start.val d' := ⟨by rw [← hcount']; exact hpost0,
        by rw [← hcount']; exact hpost1, hcount'⟩
      obtain ⟨last,xs,hdelta,hdeltaInv,houtcan,hfinish,hlen,hseq,hvalid⟩ := ih hinv'
      refine ⟨last,(l,coeff,scalar)::xs, ?_, hdeltaInv, houtcan, hfinish, ?_, ?_, ?_⟩
      · have hlocal : stateDelta d' = deltaAdd (stateDelta d) (queryDelta coeff scalar) := by
          have h0 := hupdate.1
          have h1 := hupdate.2
          apply Prod.ext
          · simpa [stateDelta, deltaAdd, queryDelta, toPushWide, toPushQm] using hupdate.1
          · simpa [stateDelta, deltaAdd, queryDelta, toPushWide, toPushQm] using hupdate.2
        rw [hdelta, hlocal]
        simp [deltaAdd, deltaSum, tupleAdd, add_assoc]
      · simp only [List.length_cons] at hlen ⊢
        omega
      · intro k hk
        cases k with
        | zero => simpa using congrArg UScalar.val hl
        | succ k =>
            have hk' : k < xs.length := by simp at hk; omega
            have ht := hseq k hk'
            have hget : ((l,coeff,scalar)::xs)[k+1]'hk = xs[k]'hk' := by simp
            rw [hget, ht, hstart]
            omega
      · intro t ht
        rcases List.mem_cons.mp ht with he | ht
        · subst t
          exact ⟨hread,hweight⟩
        · exact hvalid t ht

theorem pushZero_countInv : countInv 0 EbyKNewToPushStateABI.pushZero := by
  refine ⟨?_, ?_, rfl⟩
  · intro i hi
    have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases hc with h | h | h | h <;> subst i <;>
      simp [sumsBelowCount, EbyKNewToPushStateABI.pushZero]
  · intro i hi
    have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases hc with h | h | h | h <;> subst i <;>
      simp [sumsBelowCount, EbyKNewToPushStateABI.pushZero]

theorem successful_concrete_claim_dot_qraw_trace {H : Type}
    (inst : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Slice U8) (g : Array ClaimWide 29#usize) (point : Usize)
    (out : ClaimWide)
    (hweightCanonical : ∀ i x, Array.index_usize g i = .ok x → Concrete.Canonical x)
    (hrun : verifier.prepared_claim_dot
      (concreteOps AspisR1EbyKPushDecodedProductUpdate.QRaw) inst sem y1 g point =
      .ok (.Ok out)) :
    ∃ final : PushState, ∃ xs : List (Usize × ClaimWide × ClaimQM),
      (concreteOps AspisR1EbyKPushDecodedProductUpdate.QRaw).finishDot final = .ok out ∧
      countInv 29 final ∧ Concrete.Canonical out ∧
      stateDelta final = deltaSum xs ∧ xs.length=29 ∧
      (∀ k, ∀ hk : k < xs.length, (xs[k]'hk).1.val=k) ∧
      (∀ t ∈ xs, read (concreteOps AspisR1EbyKPushDecodedProductUpdate.QRaw)
          sem y1 point t.1 = .ok t.2.2 ∧ Array.index_usize g t.1 = .ok t.2.1) := by
  obtain ⟨initial,xsSource,hnew,hchain,hlenSource,hseqSource,hvalidSource⟩ :=
    successful_helper_has_exact_reads (concreteOps AspisR1EbyKPushDecodedProductUpdate.QRaw)
      inst sem y1 g point out hrun
  have hinitial : initial = EbyKNewToPushStateABI.pushZero := by
    apply Result.ok.inj
    calc
      .ok initial = (concreteOps AspisR1EbyKPushDecodedProductUpdate.QRaw).newDot := hnew.symm
      _ = AspisR1FinishDotConcreteOps.sourceNewDot := concreteOps_newDot _
      _ = .ok EbyKNewToPushStateABI.pushZero := AspisR1FinishDotConcreteOps.sourceNewDot_zero
  obtain ⟨final,xs,hdelta,hinv,houtcan,hfinish,hlen,hseq,hvalid⟩ :=
    chain_qraw_delta_trace sem y1 g point hweightCanonical
    (by rw [hinitial]; exact pushZero_countInv) hchain
  have hinitialDelta : stateDelta initial = (0,0) := by
    rw [hinitial]
    simp [stateDelta, castSums, EbyKNewToPushStateABI.pushZero]
  have hdelta' : stateDelta final = deltaSum xs := by
    calc
      stateDelta final = deltaAdd (stateDelta initial) (deltaSum xs) := hdelta
      _ = deltaSum xs := by rw [hinitialDelta]; simp [deltaAdd,tupleAdd]
  have hlen' : xs.length=29 := by
    have hstart : (0#usize).val=0 := rfl
    rw [hstart] at hlen
    omega
  refine ⟨final,xs,hfinish,hinv,houtcan,hdelta',hlen',?_,hvalid⟩
  intro k hk
  have hv := hseq k hk
  have hstart : (0#usize).val=0 := rfl
  simpa [hstart] using hv

theorem successful_concrete_claim_dot_decoded_product_sum {H : Type}
    (inst : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Slice U8) (g : Array ClaimWide 29#usize) (point : Usize)
    (out : ClaimWide)
    (hweightCanonical : ∀ i x, Array.index_usize g i = .ok x → Concrete.Canonical x)
    (hrun : verifier.prepared_claim_dot
      (concreteOps AspisR1EbyKPushDecodedProductUpdate.QRaw) inst sem y1 g point =
      .ok (.Ok out)) :
    ∃ xs : List (Usize × ClaimWide × ClaimQM),
      xs.length = 29 ∧
      (∀ k, ∀ hk : k < xs.length, (xs[k]'hk).1.val = k) ∧
      (∀ t ∈ xs, read (concreteOps AspisR1EbyKPushDecodedProductUpdate.QRaw)
          sem y1 point t.1 = .ok t.2.2 ∧ Array.index_usize g t.1 = .ok t.2.1) ∧
      Concrete.decode out =
        AspisR1FinishDotReturnedFieldProductV1.productSum (finishRows xs) := by
  obtain ⟨final,xs,hfinish,hinv,houtcan,hdelta,hlen,hseq,hvalid⟩ :=
    successful_concrete_claim_dot_qraw_trace inst sem y1 g point out hweightCanonical hrun
  have hsource : (do
      let f ← AspisR1FinishDotSourceABI.finishFromPush final
      Result.ok (AspisR1CurrentPreparedClaim.ClaimParser.fromFinish f)) = .ok out := by
    simpa [AspisR1S5ClaimDotConcreteAdapter.concreteOps] using hfinish
  cases hr : AspisR1FinishDotSourceABI.finishFromPush final with
  | fail e => simp [hr] at hsource
  | div => simp [hr] at hsource
  | ok f =>
      have hsource' : Result.ok (AspisR1CurrentPreparedClaim.ClaimParser.fromFinish f) = .ok out := by
        simpa [hr] using hsource
      have hout : AspisR1CurrentPreparedClaim.ClaimParser.fromFinish f = out := Result.ok.inj hsource'
      subst out
      refine ⟨xs, hlen, hseq, hvalid, ?_⟩
      have hstate :
          AspisR1FinishDotDecodedProductTrace.stateDelta final =
            AspisR1FinishDotDecodedProductTrace.deltaSum (finishRows xs) := by
        calc
          AspisR1FinishDotDecodedProductTrace.stateDelta final = stateDelta final := rfl
          _ = deltaSum xs := hdelta
          _ = AspisR1FinishDotDecodedProductTrace.deltaSum (finishRows xs) := deltaSum_finishRows xs
      calc
        Concrete.decode (AspisR1CurrentPreparedClaim.ClaimParser.fromFinish f) =
            AspisR1CurrentWide.Proof.decodeFinish f :=
          AspisR1CurrentPreparedClaim.ClaimParser.decode_from_finish f
        _ = AspisR1FinishDotReturnedDeltaDecodeV1.decodeDelta
              (AspisR1FinishDotDecodedProductTrace.stateDelta final) :=
          finishFromPush_decode_state_delta final f hr
        _ = AspisR1FinishDotReturnedDeltaDecodeV1.decodeDelta
              (AspisR1FinishDotDecodedProductTrace.deltaSum (finishRows xs)) := by rw [hstate]
        _ = AspisR1FinishDotReturnedFieldProductV1.productSum (finishRows xs) :=
          AspisR1FinishDotReturnedFieldProductV1.decodeDelta_sum (finishRows xs)

#print axioms chain_qraw_delta_trace
#print axioms pushZero_countInv
#print axioms successful_concrete_claim_dot_qraw_trace
#print axioms finishFromPush_decode_state_delta
#print axioms deltaSum_finishRows
#print axioms successful_concrete_claim_dot_decoded_product_sum

end AspisR1S5ClaimScalarConcreteQRawTrace
