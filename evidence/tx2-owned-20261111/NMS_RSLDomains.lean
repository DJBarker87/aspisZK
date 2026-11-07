import RSL_TX2_241
set_option autoImplicit false
namespace NMS_RSLDomains
open RSL RSL.TX2_241

/-- The checkpoint helper constrains the length Result, before any data getter.
This is a local source cut, not a new parent input assumption. -/
theorem checkpoint_length (account : OwnedAccount) (program : B32)
 (passed : verifierCheckpoint account program false = .ok ()) :
 account.length = .ok CHECKPOINT_BYTES := by
 unfold verifierCheckpoint at passed
 split at passed
 · cases passed
 · cases h : account.data_len with
   | error e => simp only [h] at passed; cases passed
   | ok n =>
     simp only [h] at passed
     split at passed
     · cases passed
     · rename_i hn
       have same : n = CHECKPOINT_BYTES := by simpa using hn
       simpa only [OwnedAccount.data_len, same] using h

/-- Snapshot consistency plus the actual checkpoint check gives the byte
extent at the same successful getter, without an unconditional byte-size
clause on TX2:241's input. -/
theorem checkpoint_bytes (account : OwnedAccount) (program : B32) (bytes : Bytes)
 (consistent : Consistent account)
 (passed : verifierCheckpoint account program false = .ok ())
 (read : account.bytes = .ok bytes) : bytes.length = CHECKPOINT_BYTES := by
 have hl := checkpoint_length account program passed
 have hc := consistent bytes read
 rw [hc] at hl
 exact Except.ok.inj hl

/-- The exact entered TX2:064 domain, parametric in its library.  Every
observation here is local to the 241 call path, and Root0 is taken solely from
its canonical original-input Domain at the admitted proof image. -/
theorem entered (V : V2Lib) (a : Args) (domain : Domain V a)
 (acc0 acc6 : OwnedAccount) (proofData checkpointData publicBytes : Bytes)
 (count : a.accounts.length = 7)
 (index0 : a.accounts[0]? = some acc0) (index6 : a.accounts[6]? = some acc6)
 (read0 : acc0.bytes = .ok proofData) (read6 : acc6.bytes = .ok checkpointData)
 (checkpointChecked : verifierCheckpoint acc6 a.program_id false = .ok ())
 (scanLength : Nat) (scanExtent : scanLength = PROOF_BYTES)
 (proofExtent : proofData.length = AFTERSTATE_BYTES + scanLength)
 (publicExtent : publicBytes.length = STATEMENT_BYTES) :
 Dom064 V (publicBytes, slice proofData AFTERSTATE_BYTES (AFTERSTATE_BYTES + scanLength), checkpointData) := by
 have consistent6 : Consistent acc6 := domain.1 acc6 (List.mem_of_getElem? index6)
 have ck := checkpoint_bytes acc6 a.program_id checkpointData consistent6 checkpointChecked read6
 have pr : proofData.length = PROOF_ACCOUNT_BYTES := by
   simpa only [scanExtent, PROOF_ACCOUNT_BYTES] using proofExtent
 have width : (slice proofData AFTERSTATE_BYTES (AFTERSTATE_BYTES + scanLength)).length = PROOF_BYTES := by
   simp only [slice, List.length_take, List.length_drop, proofExtent, Nat.add_sub_cancel_left,
     Nat.min_self, scanExtent]
 have root := domain.2 acc0 acc6 checkpointData proofData count index0 index6 read6 read0 pr
 unfold Dom064
 dsimp only
 apply And.intro width
 apply And.intro ck
 apply And.intro
 · rw [publicExtent]
   exact Nat.le_refl _
 · have endpoint : AFTERSTATE_BYTES + scanLength = PROOF_ACCOUNT_BYTES := by
     rw [scanExtent]
     rfl
   rw [endpoint]
   exact root

#print axioms checkpoint_length
#print axioms checkpoint_bytes
#print axioms entered
end NMS_RSLDomains
