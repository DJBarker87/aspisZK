import S3ActualLoop1TotalPrefixV1
import S3ActualLoop1OuterStepV1
import S3ZeroSeedMeaningV1
import Aeneas.Std.RangeIter

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP

namespace AspisR1GroupedPairActualFieldOpsV3.ActualLoop1OuterPrefix

open AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete
open AspisR1GroupedPairActualFieldOpsV3.ActualLoop1
open AspisR1GroupedPairActualFieldOpsV3.ActualLoop1OuterStep
open AspisR1GroupedPairActualFieldOpsV3.ZeroSeedMeaning

abbrev Wide := AspisWideTower.WideExact

def CanonicalCoefficients (coefficients : Array field.WideExact 12#usize) : Prop :=
  ∀ i : Fin 12, Canonical (coefficients.val[i.val]'(by
    have hp := coefficients.property
    change coefficients.val.length = 12 at hp
    omega))

private def actualSelectedPrefix (mask : Nat) : Nat → List Wide → Wide
  | 0, _ => 0
  | n + 1, xs => actualSelectedPrefix mask n xs +
      (if (mask / 2 ^ n) % 2 = 1 then (xs.drop n).headD 0 else 0)

private def actualGroupTerm (low : Array field.WideExact 16#usize)
    (coefficients : Array field.WideExact 12#usize) (n : Nat) : Wide :=
  if hn : n < 12 then
    let g : Fin 12 := ⟨n, hn⟩
    decode (coefficients.val[n]'(by
      have hp := coefficients.property
      change coefficients.val.length = 12 at hp
      omega)) *
    actualSelectedPrefix
      (weights.S2_INACTIVE_MASKS.val[n]'(by
        have hp := weights.S2_INACTIVE_MASKS.property
        change weights.S2_INACTIVE_MASKS.val.length = 12 at hp
        omega)).val 16 (low.val.map decode)
  else 0

private def actualOuterPrefix (low : Array field.WideExact 16#usize)
    (coefficients : Array field.WideExact 12#usize) : Nat → Wide
  | 0 => 0
  | n + 1 => actualOuterPrefix low coefficients n + actualGroupTerm low coefficients n

theorem actual_loop1_whole_prefix
    (low : Array field.WideExact 16#usize)
    (coefficients : Array field.WideExact 12#usize)
    (hlow : CanonicalLow low)
    (hcoeff : CanonicalCoefficients coefficients) :
    ∃ result,
      weights.s2_grouped_inactive_pair_loop1 actualOperations
        { start := 0#usize, «end» := 12#usize } low coefficients field.WideExact.ZERO = .ok result ∧
      Canonical result ∧ decode result = actualOuterPrefix low coefficients 12 := by
  let initialIter : core.ops.range.Range Std.Usize :=
    { start := 0#usize, «end» := 12#usize }
  let Meaning : Nat → field.WideExact → Prop := fun n pair =>
    Canonical pair ∧ decode pair = actualOuterPrefix low coefficients n
  have hwp : WP.spec
      (weights.s2_grouped_inactive_pair_loop1 actualOperations initialIter low coefficients
        field.WideExact.ZERO)
      (fun result => Canonical result ∧ decode result = actualOuterPrefix low coefficients 12) := by
    unfold weights.s2_grouped_inactive_pair_loop1
    refine loop.spec_decr_nat
      (fun s : core.ops.range.Range Std.Usize × field.WideExact => 12 - s.1.start.val)
      (fun s : core.ops.range.Range Std.Usize × field.WideExact =>
        s.1.start.val ≤ 12 ∧ s.1.end.val = 12 ∧ Meaning s.1.start.val s.2)
      (fun result => Canonical result ∧ decode result = actualOuterPrefix low coefficients 12)
      (fun s => weights.s2_grouped_inactive_pair_loop1.body actualOperations low
        coefficients s.1 s.2)
      (initialIter, field.WideExact.ZERO) ?_ ?_
    · intro s hs
      rcases s with ⟨iter, pair⟩
      rcases hs with ⟨hstartBound, hendState, hmeaning⟩
      by_cases hlt : iter.start.val < iter.end.val
      · have hnextSpec := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_some_spec
          (cloneInst := core.clone.CloneUsize) (partialOrdInst := core.cmp.PartialOrdUsize)
          (by intros; rfl) (by intros; rfl) iter hlt
        obtain ⟨nextPair, hnext, hpost⟩ := WP.spec_imp_exists hnextSpec
        rcases nextPair with ⟨opt, iterNext⟩
        rcases hpost with ⟨hopt, hnextStart, hnextEnd⟩
        have hopt' : opt = some iter.start := hopt
        subst opt
        have hgroupBound : iter.start.val < 12 := by rw [hendState] at hlt; exact hlt
        let group : Std.Usize := iter.start
        have hinnerSpec := actual_loop1_total_prefix low group (loop1InitialIter low)
          field.WideExact.ZERO hgroupBound rfl rfl rfl zero_seed_canonical zero_seed_decode hlow
        obtain ⟨weight, hweightRun, hweightPost⟩ := WP.spec_imp_exists hinnerSpec
        have hweightCanonical : Canonical weight := hweightPost.1
        have hweightMeaning : decode weight = actualSelectedPrefix
            (weights.S2_INACTIVE_MASKS.val[iter.start.val]'(by
              have hp := weights.S2_INACTIVE_MASKS.property
              change weights.S2_INACTIVE_MASKS.val.length = 12 at hp
              omega)).val 16 (low.val.map decode) := by
          change decode weight = actualSelectedPrefix _ _ _
          exact hweightPost.2
        have hcoeffBound : group.val < coefficients.length := by
          simpa [coefficients.property] using hgroupBound
        obtain ⟨coefficient, hcoeffRead, hcoeffValue⟩ :=
          WP.spec_imp_exists (Array.index_usize_spec coefficients group hcoeffBound)
        have hcoeffCanonical : Canonical coefficient := by
          rw [hcoeffValue]
          exact hcoeff ⟨group.val, by simpa [coefficients.property] using hgroupBound⟩
        obtain ⟨product, hmul, hproductCanonical, hproductValue⟩ :=
          mul_total_exact coefficient weight hcoeffCanonical hweightCanonical
        obtain ⟨pairNext, hadd, hpairNextCanonical, hpairNextValue⟩ :=
          add_total_exact pair product hmeaning.1 hproductCanonical
        have hactive : loop1ActiveCall low coefficients actualOperations group iterNext pair =
            .ok (outerCont iterNext pairNext) := by
          unfold loop1ActiveCall
          rw [show lift (Array.to_slice low) = .ok (Array.to_slice low) from rfl]
          simp only [bind_tc_ok]
          rw [show core.slice.Slice.iter (Array.to_slice low) =
            .ok ⟨Array.to_slice low, 0⟩ from rfl]
          simp only [bind_tc_ok]
          rw [show core.iter.traits.iterator.Iterator.enumerate.trait_default
            (core.iter.traits.iterator.IteratorSliceIter field.WideExact)
            ⟨Array.to_slice low, 0⟩ = .ok (loop1InitialIter low) from rfl]
          simp only [bind_tc_ok]
          rw [hweightRun]
          simp only [bind_tc_ok]
          rw [hcoeffRead]
          simp only [bind_tc_ok]
          unfold AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.actualOperations
          change (do
            let product ← AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.mul coefficient weight
            let pairNext ← AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.add pair product
            .ok (outerCont iterNext pairNext)) = .ok (outerCont iterNext pairNext)
          rw [hmul]
          simp only [bind_tc_ok]
          rw [hadd]
          rfl
        have hbody : weights.s2_grouped_inactive_pair_loop1.body actualOperations
            low coefficients iter pair = .ok (.cont (iterNext, pairNext)) := by
          rw [outer_body_eq_after_range, hnext]
          simp only [bind_tc_ok]
          exact hactive
        have hpairMeaning : decode pairNext = actualOuterPrefix low coefficients
            (iter.start.val + 1) := by
          have hcur : decode pair = actualOuterPrefix low coefficients iter.start.val := hmeaning.2
          have hterm : actualGroupTerm low coefficients iter.start.val = decode coefficient * decode weight := by
            simp [actualGroupTerm, hgroupBound, group, hcoeffValue, hweightMeaning]
          simp only [actualOuterPrefix]
          rw [hpairNextValue, hcur, hproductValue, hterm]
        rw [hbody, WP.spec_ok]
        change (iterNext.start.val ≤ 12 ∧ iterNext.end.val = 12 ∧
          Meaning iterNext.start.val pairNext) ∧
          12 - iterNext.start.val < 12 - iter.start.val
        refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
        · rw [hnextStart]; omega
        · rw [congrArg UScalar.val hnextEnd, hendState]
        · exact ⟨hpairNextCanonical, by simpa [hnextStart] using hpairMeaning⟩
        · rw [hnextStart]; omega
      · have hge : iter.start.val ≥ iter.end.val := Nat.le_of_not_gt hlt
        have hupper : iter.start.val ≤ 12 := hstartBound
        have hlower : 12 ≤ iter.start.val := by rw [hendState] at hge; exact hge
        have hge12 : iter.start.val = 12 := Nat.le_antisymm hupper hlower
        have hnextSpec := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_none_spec
          (cloneInst := core.clone.CloneUsize) (partialOrdInst := core.cmp.PartialOrdUsize)
          (by intros; rfl) iter hge
        obtain ⟨nextPair, hnext, hpost⟩ := WP.spec_imp_exists hnextSpec
        rcases nextPair with ⟨opt, iterNext⟩
        rcases hpost with ⟨rfl, rfl⟩
        rw [weights.s2_grouped_inactive_pair_loop1.body, hnext]
        simp only [bind_tc_ok, WP.spec_ok]
        exact ⟨hmeaning.1, by simpa [hge12] using hmeaning.2⟩
    · refine ⟨?_, ?_, ?_⟩
      · simp [initialIter]
      · rfl
      · change Meaning initialIter.start.val field.WideExact.ZERO
        constructor
        · exact zero_seed_canonical
        · change decode field.WideExact.ZERO = actualOuterPrefix low coefficients 0
          rw [zero_seed_decode]
          rfl
  obtain ⟨result, hresult, hmeaning⟩ := WP.spec_imp_exists hwp
  exact ⟨result, hresult, hmeaning.1, hmeaning.2⟩

#print axioms actual_loop1_whole_prefix

end AspisR1GroupedPairActualFieldOpsV3.ActualLoop1OuterPrefix
