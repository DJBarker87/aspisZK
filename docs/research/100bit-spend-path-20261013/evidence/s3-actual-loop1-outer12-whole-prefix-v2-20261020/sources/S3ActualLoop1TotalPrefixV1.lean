import S3ActualLoop1PrefixV5
import Aeneas.Std.RangeIter

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP

namespace AspisR1GroupedPairActualFieldOpsV3.ActualLoop1

open AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete

private abbrev selectedBit (mask bit : Nat) : Prop := (mask / 2 ^ bit) % 2 = 1

private def selectedPrefix (mask : Nat) : Nat → List AspisWideTower.WideExact → AspisWideTower.WideExact
  | 0, _ => 0
  | n + 1, xs => selectedPrefix mask n xs +
      (if selectedBit mask n then (xs.drop n).headD 0 else 0)

private theorem list_drop_split {α : Type} (xs : List α) (i : Nat)
    (hi : i < xs.length) : xs.drop i = xs[i] :: xs.drop (i + 1) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero => simp
      | succ i =>
          have hi' : i < xs.length := by simpa using hi
          simpa using ih i hi'


theorem actual_loop1_total_prefix
    (low : Array field.WideExact 16#usize)
    (group : Std.Usize)
    (iter0 : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter field.WideExact))
    (weight0 : field.WideExact)
    (hgroup : group.val < 12)
    (hiterSlice : iter0.iter.slice.val = low.val)
    (hiterIndex : iter0.iter.i = 0)
    (hiterCount : iter0.count.val = 0)
    (hweight0 : Canonical weight0)
    (hdecode0 : decode weight0 = 0)
    (hlow : CanonicalLow low) :
    WP.spec (weights.s2_grouped_inactive_pair_loop1_loop0 actualOperations iter0 group weight0)
      (fun result => Canonical result ∧
        decode result = selectedPrefix (weights.S2_INACTIVE_MASKS.val[group.val]'(by
          have hp := weights.S2_INACTIVE_MASKS.property
          change weights.S2_INACTIVE_MASKS.val.length = 12 at hp
          omega)).val 16 (low.val.map decode)) := by
  let mask : Std.U16 := weights.S2_INACTIVE_MASKS.val[group.val]'(by
    have hp := weights.S2_INACTIVE_MASKS.property
    change weights.S2_INACTIVE_MASKS.val.length = 12 at hp
    omega)
  let inv : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter field.WideExact) × field.WideExact → Prop :=
    fun s => s.1.count.val ≤ 16 ∧
      s.1.iter.i = s.1.count.val ∧
      s.1.iter.slice.val = low.val ∧
      Canonical s.2 ∧
      decode s.2 = selectedPrefix mask.val s.1.count.val (low.val.map decode)
  have hwp : WP.spec
      (weights.s2_grouped_inactive_pair_loop1_loop0 actualOperations iter0 group weight0)
      (fun out => Canonical out ∧ decode out = selectedPrefix mask.val 16 (low.val.map decode)) := by
    unfold weights.s2_grouped_inactive_pair_loop1_loop0
    refine loop.spec_decr_nat
      (fun s : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter field.WideExact) × field.WideExact => 16 - s.1.count.val)
      inv
      (fun out => Canonical out ∧ decode out = selectedPrefix mask.val 16 (low.val.map decode))
      (fun s => weights.s2_grouped_inactive_pair_loop1_loop0.body actualOperations group s.1 s.2)
      (iter0, weight0) ?_ ?_
    · intro s hs
      rcases s with ⟨iter, weight⟩
      rcases hs with ⟨hcountBound, hsync, hslice, hweightCan, hmeaning⟩
      change iter.count.val ≤ 16 at hcountBound
      change iter.iter.i = iter.count.val at hsync
      change iter.iter.slice.val = low.val at hslice
      by_cases hlt : iter.count.val < 16
      · have hdropExists : (low.val.drop iter.count.val).length > 0 := by
          rw [List.length_drop]
          have hp := low.property
          change low.val.length = 16 at hp
          omega
        cases htail : low.val.drop iter.count.val with
        | nil => simp [htail] at hdropExists
        | cons challenge tail =>
          have hdropLow : low.val.drop iter.count.val = challenge :: tail := htail
          have hdropIter : iter.iter.slice.val.drop iter.iter.i = challenge :: tail := by
            rw [hslice, hsync]
            exact hdropLow
          have hChallengeIndex : low.val[iter.count.val]'(by
              have hp := low.property
              change low.val.length = 16 at hp
              omega) = challenge := by
            have hsplit := list_drop_split low.val iter.count.val (by
              have hp := low.property
              change low.val.length = 16 at hp
              omega)
            rw [hdropLow] at hsplit
            have hh := congrArg List.head? hsplit
            change some challenge = some (low.val[iter.count.val]'(by
              have hp := low.property
              change low.val.length = 16 at hp
              omega)) at hh
            exact (Option.some.inj hh).symm
          have hlowChallenge : Canonical challenge := by
            have hcan := hlow ⟨iter.count.val, by
              have hp := low.property
              change low.val.length = 16 at hp
              omega⟩
            rw [← hChallengeIndex]
            exact hcan
          obtain ⟨iterNext, hnext, hsliceNext, hindexNext, hcountNext⟩ :=
            enumerate_iter_next_some iter challenge tail hdropIter
              (by
                have hmax : 16 ≤ Usize.max := by scalar_tac
                omega)
          have hmaskBound : group.val < weights.S2_INACTIVE_MASKS.length := by
            have hlen : weights.S2_INACTIVE_MASKS.length = 12 := by
              have hp := weights.S2_INACTIVE_MASKS.property
              change weights.S2_INACTIVE_MASKS.val.length = 12 at hp
              exact hp
            rw [hlen]
            exact hgroup
          obtain ⟨maskRead, hmaskRead, hmaskValue⟩ :=
            WP.spec_imp_exists (Array.index_usize_spec weights.S2_INACTIVE_MASKS group hmaskBound)
          have hmaskEq : maskRead = mask := by
            dsimp [mask]
            exact hmaskValue
          have hmask : Array.index_usize weights.S2_INACTIVE_MASKS group = .ok mask := by
            rw [← hmaskEq]
            exact hmaskRead
          obtain ⟨power, hshift, _hshiftValue⟩ :=
            WP.spec_imp_exists (UScalar.ShiftLeft_spec (1#u16) iter.count
              (UScalar.size UScalarTy.U16)
              (by
                change iter.count.val < UScalarTy.U16.numBits
                have hwidth : UScalarTy.U16.numBits = 16 := by decide
                rw [hwidth]
                exact hlt)
              rfl)
          let bitResult : Std.U16 := mask &&& power
          have hand : lift (mask &&& power) = .ok bitResult := rfl
          have hselected := actual_mask_test_matches_bit mask power bitResult iter.count hlt hshift hand
          obtain ⟨nextWeight, hadd, hnextCanonical, hdecodeAdd⟩ :=
            add_total_exact weight challenge hweightCan hlowChallenge
          have hbody := body_some_step group actualOperations iter weight challenge nextWeight
            iterNext mask power bitResult iter.count hnext hmask hshift hand hselected hadd hdecodeAdd
          have hbodyMeaning := hbody.2
          let weightNext := if bitResult != 0#u16 then nextWeight else weight
          have hweightNextCan : Canonical weightNext := by
            by_cases hb : bitResult != 0#u16 <;> simp [weightNext, hb, hnextCanonical, hweightCan]
          have hdropDecoded : (low.val.map decode).drop iter.count.val =
              decode challenge :: tail.map decode := by
            have hmap := congrArg (List.map decode) hdropLow
            simpa only [List.map_drop, List.map_cons] using hmap
          have hheadDecoded : ((low.val.map decode).drop iter.count.val).headD 0 = decode challenge := by
            rw [hdropDecoded]
            rfl
          have hmeaningNext : decode weightNext =
              selectedPrefix mask.val (iter.count.val + 1) (low.val.map decode) := by
            have hbodyValue : decode weightNext = decode weight +
                (if selectedBit mask.val iter.count.val then decode challenge else 0) := by
              simpa [weightNext, selectedBit] using hbodyMeaning
            calc
              decode weightNext = decode weight +
                  (if selectedBit mask.val iter.count.val then decode challenge else 0) := hbodyValue
              _ = selectedPrefix mask.val iter.count.val (low.val.map decode) +
                  (if selectedBit mask.val iter.count.val then decode challenge else 0) := by rw [hmeaning]
              _ = selectedPrefix mask.val (iter.count.val + 1) (low.val.map decode) := by
                rw [selectedPrefix]
                rw [hheadDecoded]
          rw [hbody.1, WP.spec_ok]
          change inv (iterNext, weightNext) ∧ 16 - iterNext.count.val < 16 - iter.count.val
          refine ⟨?_, ?_⟩
          · refine ⟨?_, ?_, ?_, hweightNextCan, ?_⟩
            · rw [hcountNext]
              omega
            · rw [hindexNext, hsync, hcountNext]
            · rw [hsliceNext, hslice]
            · rw [hcountNext]
              exact hmeaningNext
          · rw [hcountNext]
            omega
      · have hge : 16 ≤ iter.count.val := Nat.le_of_not_gt hlt
        have hcountEq : iter.count.val = 16 := Nat.le_antisymm hcountBound hge
        have hindexEq : iter.iter.i = 16 := by omega
        have hinnerNone :
            (core.iter.traits.iterator.IteratorSliceIter field.WideExact).next iter.iter
              ⦃ (p : Option field.WideExact × core.slice.iter.Iter field.WideExact) =>
                p.1 = none ∧ p.2 = iter.iter ⦄ := by
          change core.slice.iter.IteratorSliceIter.next iter.iter ⦃ (p :
            Option field.WideExact × core.slice.iter.Iter field.WideExact) =>
              p.1 = none ∧ p.2 = iter.iter ⦄
          unfold core.slice.iter.IteratorSliceIter.next
          have hlenVal : iter.iter.slice.len.val = 16 := by
            rw [Slice.len_val]
            have hp := low.property
            change low.val.length = 16 at hp
            change iter.iter.slice.val.length = 16
            rw [hslice]
            exact hp
          have hlen : iter.iter.slice.len = 16#usize := UScalar.eq_of_val_eq hlenVal
          simp [hindexEq, hlen]
        have hnoneSpec := core.iter.adapters.enumerate.IteratorEnumerate.next_none_spec
          (core.iter.traits.iterator.IteratorSliceIter field.WideExact) iter iter.iter hinnerNone
        obtain ⟨pair, hnext, hpost⟩ := WP.spec_imp_exists hnoneSpec
        rcases pair with ⟨opt, iterNext⟩
        rcases hpost with ⟨hopt, _hiterNext, _hcountNext⟩
        subst opt
        rw [weights.s2_grouped_inactive_pair_loop1_loop0.body, hnext]
        simp only [bind_tc_ok, WP.spec_ok]
        exact ⟨hweightCan, by simpa [hcountEq] using hmeaning⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hiterCount]
        omega
      · rw [hiterIndex, hiterCount]
      · exact hiterSlice
      · exact hweight0
      · rw [hiterCount]
        simpa [selectedPrefix] using hdecode0
  simpa [mask] using hwp

#print axioms actual_loop1_total_prefix

end AspisR1GroupedPairActualFieldOpsV3.ActualLoop1
