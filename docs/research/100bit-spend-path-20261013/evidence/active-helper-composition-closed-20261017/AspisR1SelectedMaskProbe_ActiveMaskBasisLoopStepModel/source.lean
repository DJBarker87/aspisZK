import AspisR1SelectedMaskProbe.ActiveMaskBasisSourceSlice
import AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts
import ExtractedMaskQM31Exact
import ArrayUpdateCanonicalExact

open Aeneas Aeneas.Std Result ControlFlow WP
open AspisR1SelectedMaskProbe
namespace AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStepModel

abbrev QM := field.QM31
abbrev CanonicalQM := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev CanonicalArray {n : Usize} (a : Array QM n) :=
  AspisR1.ArrayUpdateCanonicalExact.CanonicalArray a

def cellAt (a : Array QM 7#usize) (j : Fin 7) : QM :=
  a.val[j.val]'(by simpa [a.property] using j.isLt)

def generatedCoordinateMatch (mask : Std.U16) : Result Usize :=
  match mask with
  | 6144#uscalar => ok 0#usize
  | 6145#uscalar => ok 1#usize
  | 4097#uscalar => ok 2#usize
  | 2048#uscalar => ok 3#usize
  | 2049#uscalar => ok 4#usize
  | 26214#uscalar => ok 5#usize
  | 1749#uscalar => ok 6#usize
  | _ => fail Error.panic

private theorem generated_match_of_member
    (mask : Std.U16) (coordinate : Usize)
    (hmember : mask = 6144#u16 ∨ mask = 6145#u16 ∨ mask = 4097#u16 ∨
      mask = 2048#u16 ∨ mask = 2049#u16 ∨ mask = 26214#u16 ∨
      mask = 1749#u16)
    (hmatch : AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.matchCoordinate mask =
      .ok coordinate) : generatedCoordinateMatch mask = .ok coordinate := by
  rcases hmember with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · have hc : coordinate = 0#usize := by
      have hh := hmatch
      simp [AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.matchCoordinate, h0] at hh
      exact (Result.ok.inj hh).symm
    rw [h0, hc]
    rfl
  · have hc : coordinate = 1#usize := by
      have hh := hmatch
      simp [AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.matchCoordinate, h1] at hh
      exact (Result.ok.inj hh).symm
    rw [h1, hc]
    rfl
  · have hc : coordinate = 2#usize := by
      have hh := hmatch
      simp [AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.matchCoordinate, h2] at hh
      exact (Result.ok.inj hh).symm
    rw [h2, hc]
    rfl
  · have hc : coordinate = 3#usize := by
      have hh := hmatch
      simp [AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.matchCoordinate, h3] at hh
      exact (Result.ok.inj hh).symm
    rw [h3, hc]
    rfl
  · have hc : coordinate = 4#usize := by
      have hh := hmatch
      simp [AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.matchCoordinate, h4] at hh
      exact (Result.ok.inj hh).symm
    rw [h4, hc]
    rfl
  · have hc : coordinate = 5#usize := by
      have hh := hmatch
      simp [AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.matchCoordinate, h5] at hh
      exact (Result.ok.inj hh).symm
    rw [h5, hc]
    rfl
  · have hc : coordinate = 6#usize := by
      have hh := hmatch
      simp [AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.matchCoordinate, h6] at hh
      exact (Result.ok.inj hh).symm
    rw [h6, hc]
    rfl

private theorem index_usize_ok {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (hi : i.val < n.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

private theorem usize_add_result (a b : Usize) (hsum : a.val + b.val ≤ Usize.max) :
    ∃ c : Usize, UScalar.add a b = .ok c ∧ c.val = a.val + b.val := by
  have hchecked : (a + b : Result Usize) ⦃ z => z.val = a.val + b.val ⦄ := by
    apply UScalar.add_spec
    simpa only [UScalar.max_USize_eq] using hsum
  obtain ⟨c, hc, hval⟩ := WP.spec_imp_exists hchecked
  refine ⟨c, ?_, hval⟩
  change (a + b : Result Usize) = .ok c
  exact hc

/-- Exact successful body step for the generated high-coordinate loop.  It
records the actual checked field addition and array update, not merely their
mathematical specification. -/
theorem loop0_body_step_model
    (self : pool_v1.pair_forest_copy_terminal.Selectors)
    (highSums : Array QM 7#usize) (block : Usize)
    (hblock : block.val < 64)
    (hself : CanonicalArray self.high)
    (hsums : CanonicalArray highSums) :
    ∃ coordinate : Usize, ∃ hcoordinate : coordinate.val < 7,
      coordinate = AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.modelCoordinate
        (R0P.copyActiveRowMasks ⟨block.val, hblock⟩) ∧
      ∃ added : QM, ∃ updated : Array QM 7#usize, ∃ block1 : Usize,
      pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop0.body
        self highSums block = .ok (.cont (updated, block1)) ∧
      UScalar.add block 1#usize = .ok block1 ∧
      field.QM31.add
        (highSums.val[coordinate.val]'(by
          simpa [highSums.property] using hcoordinate))
        (self.high.val[block.val]'(by
          simpa [self.high.property] using hblock)) = .ok added ∧
      CanonicalQM added ∧
      CanonicalArray updated ∧
      updated = highSums.set coordinate added := by
  let row : Fin 64 := ⟨block.val, hblock⟩
  let mask := AspisR1SelectedMaskProbe.ActiveMaskBasisLoopProof.sourceMask row
  let coordinate := AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.modelCoordinate
    (R0P.copyActiveRowMasks row)
  have h64 : (64#usize).val = 64 := by scalar_tac
  have h7 : (7#usize).val = 7 := by scalar_tac
  have hblockU : block.val < (64#usize).val := by simpa [h64] using hblock
  have hmaskread : Array.index_usize
      pool_v1.pair_forest_copy_terminal.constants.ACTIVE_ROW_MASKS block = .ok mask := by
    have h := index_usize_ok
      pool_v1.pair_forest_copy_terminal.constants.ACTIVE_ROW_MASKS block hblockU
    simpa [mask, row, AspisR1SelectedMaskProbe.ActiveMaskBasisLoopProof.sourceMask] using h
  have hmaskMatch := AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.source_match_coordinate row
  have hmatch : AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.matchCoordinate mask = .ok coordinate := by
    simpa [mask, coordinate] using hmaskMatch
  have hcoordinate : coordinate.val < 7 := by
    rcases AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.source_mask_member row with
      hmask | hmask | hmask | hmask | hmask | hmask | hmask
    all_goals
      have htable := AspisR1SelectedMaskProbe.ActiveMaskBasisLoopProof.source_mask_table row
      have hcopy : R0P.copyActiveRowMasks row =
          (AspisR1SelectedMaskProbe.ActiveMaskBasisLoopProof.sourceMask row).val :=
        htable.symm
      have hnum := congrArg UScalar.val hmask
      rw [hnum] at hcopy
      simp [coordinate,
        AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.modelCoordinate,
        hcopy]
  have hcoordinateU : coordinate.val < (7#usize).val := by simpa [h7] using hcoordinate
  have hsumsLen : highSums.length = (7#usize).val := by
    simpa [highSums.property]
  have hcoordinateArray : coordinate.val < highSums.length := by
    rw [hsumsLen]
    exact hcoordinateU
  let old := highSums.val[coordinate.val]'(by
    simpa [highSums.property] using hcoordinateU)
  let highCell := self.high.val[block.val]'(by
    simpa [self.high.property] using hblockU)
  have hold : Array.index_usize highSums coordinate = .ok old := by
    exact index_usize_ok highSums coordinate hcoordinateU
  have hhighCell : Array.index_usize self.high block = .ok highCell := by
    exact index_usize_ok self.high block hblockU
  have holdCanonical : CanonicalQM old := by
    apply hsums ⟨coordinate.val, hcoordinateU⟩
  have hhighCanonical : CanonicalQM highCell := by
    apply hself ⟨block.val, hblockU⟩
  obtain ⟨added, hadd, haddCanonical, _haddValue⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact old highCell
      holdCanonical hhighCanonical
  obtain ⟨updated, hupdate, hupdatedCanonical, _hframe⟩ :=
    AspisR1.ArrayUpdateCanonicalExact.update_success highSums coordinate added
      hcoordinateU hsums haddCanonical
  have hset : updated = highSums.set coordinate added := by
    obtain ⟨updated', hupdate', hset'⟩ :=
      WP.spec_imp_exists (Array.update_spec highSums coordinate added hcoordinateArray)
    have heq : updated = updated' := Result.ok.inj (hupdate.symm.trans hupdate')
    rw [heq]
    exact hset'
  have hincBound : block.val + 1 ≤ Usize.max := by
    have hmax := Usize.cMax_bound_concrete.1
    omega
  obtain ⟨block1, hinc, _hincval⟩ := usize_add_result block 1#usize hincBound
  have hlen : Slice.len (Array.to_slice
      pool_v1.pair_forest_copy_terminal.constants.ACTIVE_ROW_MASKS) = 64#usize := by
    apply UScalar.eq_of_val_eq
    simp [Slice.len, Slice.length, Array.to_slice,
      pool_v1.pair_forest_copy_terminal.constants.ACTIVE_ROW_MASKS]
  have hlt : block < Slice.len (Array.to_slice
      pool_v1.pair_forest_copy_terminal.constants.ACTIVE_ROW_MASKS) := by
    rw [hlen]
    scalar_tac
  have hsourceLt : block < 64#usize := by
    rw [← hlen]
    exact hlt
  have hinc' : (block + 1#usize : Result Usize) = .ok block1 := by
    change UScalar.add block 1#usize = .ok block1
    exact hinc
  have hmember : mask = 6144#u16 ∨ mask = 6145#u16 ∨ mask = 4097#u16 ∨
      mask = 2048#u16 ∨ mask = 2049#u16 ∨ mask = 26214#u16 ∨ mask = 1749#u16 := by
    simpa [mask] using
      AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.source_mask_member row
  have hmatchBody : generatedCoordinateMatch mask = .ok coordinate :=
    generated_match_of_member mask coordinate hmember hmatch
  refine ⟨coordinate, hcoordinate, rfl, added, updated, block1, ?_, hinc, hadd,
    haddCanonical, hupdatedCanonical, hset⟩
  · simp only [pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop0.body,
      lift, bind_tc_ok, hlen, if_pos hsourceLt, hmaskread, bind_tc_ok]
    change (do
      let c ← generatedCoordinateMatch mask
      let q ← Array.index_usize highSums c
      let q1 ← Array.index_usize self.high block
      let q2 ← field.QM31.add q q1
      let a ← Array.update highSums c q2
      let block1' ← block + 1#usize
      ok (ControlFlow.cont (a, block1'))) = ok (ControlFlow.cont (updated, block1))
    simp only [hmatchBody, bind_tc_ok, hold, bind_tc_ok,
      hhighCell, bind_tc_ok, hadd, bind_tc_ok, hupdate, bind_tc_ok, hinc']

#print axioms loop0_body_step_model
end AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStepModel
