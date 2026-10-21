import S4AllFourHeadDecodingV1
import S4TailFieldProductRootV1

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1FastDotsHeadDecodeV1

abbrev U32 := Std.U32
abbrev TowerWide := AspisR1FastDotsTailFieldProductRootV1.TowerWide

private theorem xs_length (xs : Array U32 8#usize) : xs.val.length = 8 := by
  have hsize : (8#usize).val = 8 := by scalar_tac
  simpa [hsize] using xs.property
private def word0 (xs : Array U32 8#usize) : U32 :=
  xs.val[0]'(by have h := xs_length xs; omega)
private def word1 (xs : Array U32 8#usize) : U32 :=
  xs.val[1]'(by have h := xs_length xs; omega)
private def word2 (xs : Array U32 8#usize) : U32 :=
  xs.val[2]'(by have h := xs_length xs; omega)
private def word3 (xs : Array U32 8#usize) : U32 :=
  xs.val[3]'(by have h := xs_length xs; omega)
private def word4 (xs : Array U32 8#usize) : U32 :=
  xs.val[4]'(by have h := xs_length xs; omega)
private def word5 (xs : Array U32 8#usize) : U32 :=
  xs.val[5]'(by have h := xs_length xs; omega)
private def word6 (xs : Array U32 8#usize) : U32 :=
  xs.val[6]'(by have h := xs_length xs; omega)
private def word7 (xs : Array U32 8#usize) : U32 :=
  xs.val[7]'(by have h := xs_length xs; omega)

private def decodedParts (xs : Array U32 8#usize) : TowerWide :=
  AspisR1FastDotsTailFieldProductRootV1.wideDecoded
    (AspisR1FastDotsN8WideFromLimbsABI.finishToCurrent
      (AspisR1EbyKFinish.Proof.wideFromParts
        (word0 xs) (word1 xs) (word2 xs) (word3 xs)
        (word4 xs) (word5 xs) (word6 xs) (word7 xs)))

private abbrev M31 := AspisV8R15.ExactTowerBase.M31Exact
private def residue (ds : List (List AspisR1FastDotsOuterFoldTraceV2.Contribution))
    (j : Fin 8) : M31 :=
  (AspisR1.FastDotFoldedBatches.fullSum
      (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds j) %
    AspisR1BatchedFoldArithmetic.modulus : M31)
private def decodedResidues
    (ds : List (List AspisR1FastDotsOuterFoldTraceV2.Contribution)) : TowerWide :=
  ⟨AspisV8R17.QM31WordTower.embedQ
      ((residue ds ⟨0,by decide⟩,residue ds ⟨1,by decide⟩),
       (residue ds ⟨2,by decide⟩,residue ds ⟨3,by decide⟩)),
   AspisV8R17.QM31WordTower.embedQ
      ((residue ds ⟨4,by decide⟩,residue ds ⟨5,by decide⟩),
       (residue ds ⟨6,by decide⟩,residue ds ⟨7,by decide⟩))⟩

theorem decodedParts_eq_coordinate_decode (xs : Array U32 8#usize) :
    decodedParts xs =
      ⟨AspisV8R17.QM31WordTower.embedQ
          (((word0 xs).val,(word1 xs).val),((word2 xs).val,(word3 xs).val)),
       AspisV8R17.QM31WordTower.embedQ
          (((word4 xs).val,(word5 xs).val),((word6 xs).val,(word7 xs).val))⟩ := by
  rfl

theorem slot_body_decodes_to_packed_coordinates
    (ops : AspisR1FastDotsAllFourHeadDecodingV1.Ops)
    (a : Array Std.U8 608#usize)
    (g : Array AspisR1FastDotsAllFourHeadDecodingV1.Wide 29#usize)
    (slot : Usize) (witnessTag : AspisR1FastDotsAllFourHeadDecodingV1.Wide)
    (hw : AspisR1FastDotsAllFourHeadDecodingV1.SlotHeadWitness ops a g slot witnessTag) :
    ∃ body : AspisR1FastDotsAllFourHeadDecodingV1.Wide,
      ∃ xs : Array U32 8#usize,
      AspisR1CurrentWide.Proof.decodeWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE body) = decodedParts xs := by
  rcases hw with ⟨_iter,_limbs,xs,body,_ds,_starts,_hstep,_hbase,_harray,
      _hbody,htrace,hseven,hmap,hcanon,hpack⟩
  refine ⟨body,xs, ?_⟩
  rw [AspisR1FastDotsTailFieldProductRootV1.current_decode_eq]
  rw [hpack]
  rfl

theorem slot_packed_decode_matches_batch_residues
    (xs : Array U32 8#usize)
    (ds : List (List AspisR1FastDotsOuterFoldTraceV2.Contribution))
    (hmap : xs.val.map (fun word => word.val) =
      [AspisR1.FastDotFoldedBatches.fullSum
          (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨0,by decide⟩) % AspisR1BatchedFoldArithmetic.modulus,
       AspisR1.FastDotFoldedBatches.fullSum
          (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨1,by decide⟩) % AspisR1BatchedFoldArithmetic.modulus,
       AspisR1.FastDotFoldedBatches.fullSum
          (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨2,by decide⟩) % AspisR1BatchedFoldArithmetic.modulus,
       AspisR1.FastDotFoldedBatches.fullSum
          (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨3,by decide⟩) % AspisR1BatchedFoldArithmetic.modulus,
       AspisR1.FastDotFoldedBatches.fullSum
          (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨4,by decide⟩) % AspisR1BatchedFoldArithmetic.modulus,
       AspisR1.FastDotFoldedBatches.fullSum
          (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨5,by decide⟩) % AspisR1BatchedFoldArithmetic.modulus,
       AspisR1.FastDotFoldedBatches.fullSum
          (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨6,by decide⟩) % AspisR1BatchedFoldArithmetic.modulus,
       AspisR1.FastDotFoldedBatches.fullSum
          (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨7,by decide⟩) % AspisR1BatchedFoldArithmetic.modulus]) :
    decodedParts xs = decodedResidues ds := by
  have h0 : (word0 xs).val = AspisR1.FastDotFoldedBatches.fullSum
      (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨0,by decide⟩) %
      AspisR1BatchedFoldArithmetic.modulus := by
    have h := congrArg (fun l : List Nat => l[0]?) hmap
    simpa [List.getElem?_map, word0, xs_length] using h
  have h1 : (word1 xs).val = AspisR1.FastDotFoldedBatches.fullSum
      (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨1,by decide⟩) %
      AspisR1BatchedFoldArithmetic.modulus := by
    have h := congrArg (fun l : List Nat => l[1]?) hmap
    simpa [List.getElem?_map, word1, xs_length] using h
  have h2 : (word2 xs).val = AspisR1.FastDotFoldedBatches.fullSum
      (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨2,by decide⟩) %
      AspisR1BatchedFoldArithmetic.modulus := by
    have h := congrArg (fun l : List Nat => l[2]?) hmap
    simpa [List.getElem?_map, word2, xs_length] using h
  have h3 : (word3 xs).val = AspisR1.FastDotFoldedBatches.fullSum
      (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨3,by decide⟩) %
      AspisR1BatchedFoldArithmetic.modulus := by
    have h := congrArg (fun l : List Nat => l[3]?) hmap
    simpa [List.getElem?_map, word3, xs_length] using h
  have h4 : (word4 xs).val = AspisR1.FastDotFoldedBatches.fullSum
      (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨4,by decide⟩) %
      AspisR1BatchedFoldArithmetic.modulus := by
    have h := congrArg (fun l : List Nat => l[4]?) hmap
    simpa [List.getElem?_map, word4, xs_length] using h
  have h5 : (word5 xs).val = AspisR1.FastDotFoldedBatches.fullSum
      (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨5,by decide⟩) %
      AspisR1BatchedFoldArithmetic.modulus := by
    have h := congrArg (fun l : List Nat => l[5]?) hmap
    simpa [List.getElem?_map, word5, xs_length] using h
  have h6 : (word6 xs).val = AspisR1.FastDotFoldedBatches.fullSum
      (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨6,by decide⟩) %
      AspisR1BatchedFoldArithmetic.modulus := by
    have h := congrArg (fun l : List Nat => l[6]?) hmap
    simpa [List.getElem?_map, word6, xs_length] using h
  have h7 : (word7 xs).val = AspisR1.FastDotFoldedBatches.fullSum
      (AspisR1FastDotsOuterFoldTraceV2.rawBatchLists ds ⟨7,by decide⟩) %
      AspisR1BatchedFoldArithmetic.modulus := by
    have h := congrArg (fun l : List Nat => l[7]?) hmap
    simpa [List.getElem?_map, word7, xs_length] using h
  rw [decodedParts_eq_coordinate_decode]
  unfold decodedResidues residue
  rw [h0,h1,h2,h3,h4,h5,h6,h7]
  have hmod : AspisR1BatchedFoldArithmetic.modulus = AspisV8R17.RawReducer.P := rfl
  simp [hmod, ZMod.natCast_mod]

theorem slot_body_decodes_to_exact_batch_residues
    (ops : AspisR1FastDotsAllFourHeadDecodingV1.Ops)
    (a : Array Std.U8 608#usize)
    (g : Array AspisR1FastDotsAllFourHeadDecodingV1.Wide 29#usize)
    (slot : Usize) (witnessTag : AspisR1FastDotsAllFourHeadDecodingV1.Wide)
    (hw : AspisR1FastDotsAllFourHeadDecodingV1.SlotHeadWitness ops a g slot witnessTag) :
    ∃ body : AspisR1FastDotsAllFourHeadDecodingV1.Wide,
      ∃ ds : List (List AspisR1FastDotsOuterFoldTraceV2.Contribution),
        ds.length = 7 ∧
        AspisR1CurrentWide.Proof.decodeWide
          (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE body) = decodedResidues ds := by
  rcases hw with ⟨_iter,_limbs,xs,body,_ds,_starts,_hstep,_hbase,_harray,
      _hbody,htrace,hseven,hmap,hcanon,hpack⟩
  refine ⟨body,_ds,hseven,?_⟩
  rw [AspisR1FastDotsTailFieldProductRootV1.current_decode_eq,hpack]
  change decodedParts xs = decodedResidues _ds
  rw [decodedParts_eq_coordinate_decode]
  exact slot_packed_decode_matches_batch_residues xs _ds hmap

#print axioms decodedParts_eq_coordinate_decode
#print axioms slot_body_decodes_to_packed_coordinates
#print axioms slot_packed_decode_matches_batch_residues
#print axioms slot_body_decodes_to_exact_batch_residues

end AspisR1FastDotsHeadDecodeV1
