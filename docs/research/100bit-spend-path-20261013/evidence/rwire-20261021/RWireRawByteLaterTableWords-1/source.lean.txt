import RWireRawByteTableWords
import OracleProgramRecording
import TraceAppend

/-! Prior commitment words can be reconstructed from any later first-read
table. This supplies the chronological word-data interface needed by a
prefix decoder: it need not retain separate copies of older tables. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RWireRawByteLaterTableWords

open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.AdaptiveFirstReadLaw
open BinRawByteCutRecovery BinRawByteCutStability RWireRawByteTableWords

/-- A prefix containing the commitment already recovers the eventual word. -/
theorem recover_prefix_eq_full (iv : State) (H : Bytes → State)
    (pre post : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ pre ++ post, q.2 = H q.1)
    (hQ : firstReads emptyTable (pre ++ post) ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q)
      emptyTable (pre ++ post))
    (tag : BinMerkle32Path.Byte) (width : Nat) (slots : List (Fin 2)) (root : State)
    (frame : Bytes) (j : Fin 5) (hframe : Read pre frame)
    (hpred : BinRawByteCollisionTargets.pred j frame = some root) :
    recoverAt tag width pre slots root = recoverAt tag width (pre ++ post) slots root := by
  have hcp : ∀ q ∈ pre, q.2 = H q.1 := fun q hq =>
    hcons q (List.mem_append.mpr (Or.inl hq))
  have hQp : firstReads emptyTable pre ≤ Q :=
    (TraceAppend.firstReads_le_append emptyTable pre post).trans hQ
  have houtp : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q)
      emptyTable pre := fun h => hout (TraceAppend.hitsBad_of_prefix _ _ pre post h)
  have hframeFull : Read (pre ++ post) frame := by
    change frame ∈ (pre ++ post).map Prod.fst
    rw [List.map_append]
    exact List.mem_append.mpr (Or.inl hframe)
  have hcut : cut (pre ++ post) frame = cut pre frame :=
    OracleProgramRecording.cut_append_of_read frame pre post hframe
  calc
    recoverAt tag width pre slots root = recoverAt tag width (cut pre frame) slots root :=
      (recover_stable iv H pre Q hcp hQp houtp tag width slots root frame j hframe hpred).symm
    _ = recoverAt tag width (cut (pre ++ post) frame) slots root := by rw [hcut]
    _ = recoverAt tag width (pre ++ post) slots root :=
      recover_stable iv H (pre ++ post) Q hcons hQ hout tag width slots root
        frame j hframeFull hpred

/-- The decoder's one current table suffices for every earlier commitment
word, simultaneously over all Merkle coordinates. -/
theorem recover_later_table_eq_full (iv : State) (H : Bytes → State)
    (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q)
      emptyTable tr)
    (tag : BinMerkle32Path.Byte) (width : Nat) (root : State)
    (frame current : Bytes) (j : Fin 5)
    (hbefore : Before tr frame current)
    (hpred : BinRawByteCollisionTargets.pred j frame = some root) :
    (fun slots => recoverFromTable (tableBefore emptyTable tr current) tag width slots root) =
      (fun slots => recoverAt tag width tr slots root) := by
  funext slots
  rw [recover_table_eq_cut iv H tr Q current hcons hQ hout]
  have hsplit : cut tr current ++ tr.drop (firstIdx current tr) = tr :=
    List.take_append_drop _ _
  have hframe : Read (cut tr current) frame := (read_cut_iff tr current frame).mpr hbefore
  have h := recover_prefix_eq_full iv H (cut tr current) (tr.drop (firstIdx current tr)) Q
    (by simpa only [hsplit] using hcons) (by simpa only [hsplit] using hQ)
    (by simpa only [hsplit] using hout) tag width slots root frame j hframe hpred
  simpa only [hsplit] using h

#print axioms recover_prefix_eq_full
#print axioms recover_later_table_eq_full

end AspisR1.RWireRawByteLaterTableWords
end
