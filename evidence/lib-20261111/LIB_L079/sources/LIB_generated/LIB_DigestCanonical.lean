import LIB_DigestBytes
set_option autoImplicit false
namespace LIB_DigestCanonical
open Aeneas Aeneas.Std
abbrev bytes (b : Array U8 32#usize) : RSL.Bytes := b.val.map NND_Carrier.byte
def word (b : Array U8 32#usize) (i : Nat) : UInt32 :=
 RSL.le32 ((bytes b).getD (4*i) 0) ((bytes b).getD (4*i+1) 0)
   ((bytes b).getD (4*i+2) 0) ((bytes b).getD (4*i+3) 0)
def option (r : core.result.Result (Array U32 8#usize)
    AspisR1TerminalDecoder.atomic_statement.AtomicStatementError) : Option RSL.Digest :=
 match r with | .Ok a => some (a.val.map NND_Carrier.word) | .Err _ => none
theorem word_exact (b : Array U8 32#usize) (i : Nat) (bound : i < 8) :
 NND_Carrier.word (NFY_NBG_WideBytes.word b i) = word b i := LIB_DigestBytes.word b i bound
theorem noncanonical (b : Array U8 32#usize) (i : Nat) (bound : i < 8) :
 NFY_NBG_WideBytes.word b i >= NFY_NBP_DecodeWord.P ↔ ¬word b i < RSL.P31 := by
 have h := NND_Carrier.word_lt (NFY_NBG_WideBytes.word b i) NFY_NBP_DecodeWord.P
 rw [word_exact b i bound] at h
 change (NFY_NBG_WideBytes.word b i < NFY_NBP_DecodeWord.P ↔ word b i < RSL.P31) at h
 exact (not_lt).symm.trans (not_congr h)
theorem limbs (b : Array U8 32#usize) :
 (NFY_NBG_WideBytes.limbs b).val.map NND_Carrier.word = (List.range 8).map (word b) := by
 simp (disch := omega) only [NFY_NBG_WideBytes.limbs,Array.make,List.map_cons,List.map_nil,word_exact]
 rfl
/-- Literal canonical decoder transcription, at identical32 input bytes. -/
theorem model (b : Array U8 32#usize) :
 option (NFY_NBP_DigestDecode.decoded b) = RSL.TX2_217.decodeDigestCanonical (bytes b) := by
 unfold NFY_NBP_DigestDecode.decoded RSL.TX2_217.decodeDigestCanonical
 change option (if NFY_NBG_WideBytes.word b 0 >= NFY_NBP_DecodeWord.P then _ else _) = _
 simp (disch := omega) only [noncanonical]
 change option (if ¬word b 0 < RSL.P31 then _ else _) =
   if ((List.range 8).map (word b)).all (fun w => decide (w < RSL.P31))
   then some ((List.range 8).map (word b)) else none
 split_ifs <;> simp_all [option,limbs,List.range_succ]
/-- CLOSED146 result is kept separate from the graph's value definition. -/
theorem source (b : Array U8 32#usize) :
 LIB_Carriers.resultObs option []
  (AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical b) =
 ⟨.ret (RSL.TX2_217.decodeDigestCanonical (bytes b)),[]⟩ := by
 rw [NFY_NBP_DigestDecode.result,LIB_Carriers.result_ok,model]
#print axioms word_exact
#print axioms noncanonical
#print axioms limbs
#print axioms model
#print axioms source
end LIB_DigestCanonical
