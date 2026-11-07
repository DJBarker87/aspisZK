import LIB_DigestBytes
import LIB_DigestGuards
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
theorem option_ite (p : Prop) [Decidable p]
 (x y : core.result.Result (Array U32 8#usize)
    AspisR1TerminalDecoder.atomic_statement.AtomicStatementError) :
 option (if p then x else y) = if p then option x else option y := by
 by_cases h : p <;> simp only [h,if_true,if_false]
#print axioms option_ite
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
 let ws := (List.range 8).map (word b)
 have rhs : RSL.TX2_217.decodeDigestCanonical (bytes b) =
     LIB_DigestGuards.guarded (ws.map (fun w => decide (w < RSL.P31))) ws := by
   rw [LIB_DigestGuards.all]
   simp only [List.all_map,Function.comp_def]
   rfl
 rw [rhs]
 unfold NFY_NBP_DigestDecode.decoded
 simp (disch := omega) only [noncanonical,option_ite,ite_not]
 simp only [option,limbs]
 change _ = LIB_DigestGuards.guarded
   [decide (word b 0 < RSL.P31),decide (word b 1 < RSL.P31),
    decide (word b 2 < RSL.P31),decide (word b 3 < RSL.P31),
    decide (word b 4 < RSL.P31),decide (word b 5 < RSL.P31),
    decide (word b 6 < RSL.P31),decide (word b 7 < RSL.P31)] ws
 simp only [LIB_DigestGuards.guarded,decide_eq_true_eq]
 all_goals rfl
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
