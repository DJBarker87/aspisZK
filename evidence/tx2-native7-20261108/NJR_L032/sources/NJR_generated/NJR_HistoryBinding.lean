import NJO_COMBINED_IMPORT
import NJR_HistoryFromScan
import MultiproofConeByteEquality
set_option autoImplicit false
noncomputable section
namespace NJR_HistoryBinding
open Aeneas Aeneas.Std Result AspisR1
open OraclePortCompactDraft MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- The first proof's actual parser facts already exported by the headline
supply strict scanning, without a new successful-scan root premise. -/
theorem parsed (proof : Slice U8) (facts : T2R_Parser.Facts proof) :
 NJR_FinishWindows.History proof := by
 obtain ⟨expanded,pre,accepted,rows,parsed⟩:=facts
 have header:=((OraclePortHeader.accepts_iff _).mp (parse_header _ _ parsed).1).1
 have length : proof.val.length=57607 := by
  simpa only [bytesOf,List.length_map] using header
 have scanned : scan (bytesOf proof.val) := by
  by_contra missing
  have rejected : parse (bytesOf proof.val)=none := by
   by_cases h : OraclePortHeader.accepts (bytesOf proof.val)=false
   · simp only [parse,h,if_true]
   · simp only [parse,h,if_false,missing,if_true,Bool.true_eq_false,not_false_eq_true]
  rw [rejected] at parsed
  cases parsed
 have checked : Op4P_Install.sourceBody proof=ok (.Ok ()) := by
  unfold Op4P_Install.sourceBody
  rw [Op4P_Refinement.reference_total proof length]
  simp only [scanned,if_true,bind_tc_ok]
 exact NJR_HistoryFromScan.source proof length checked

/-- Exact SAME-proof bytes suffice. This is forward transport, not inversion
of independent logs or an inference from a pointer/digest. -/
theorem current (first second : Slice U8) (facts : T2R_Parser.Facts first)
 (same : bytesOf second.val=bytesOf first.val) : NJR_FinishWindows.History second := by
 have sameSlice : second=first := Subtype.ext (MultiproofConeByteEquality.bytes_injective same)
 rw [sameSlice]
 exact parsed first facts

/-- Existing P2Prime is conditional binding for this pair. It is NOT added as
an unconditional root premise; the caller must establish its admitted branch. -/
theorem by_p2prime (H : Bytes → State) (first pub second public2 : Slice U8)
 (facts : T2R_Parser.Facts first)
 (binding : S2W_AuthenticatedInputs.P2Prime H first pub second public2)
 (matched : R9PoolRuntimeBinding.digestMatches H
  ⟨bytesOf first.val,bytesOf pub.val⟩ ⟨bytesOf second.val,bytesOf public2.val⟩) :
 NJR_FinishWindows.History second :=
 current first second facts (binding.binding matched).1

/-- Tiny abstract-hash counterexample to the missing logical inference only.
This is not a SHA256 collision or a counterexample to the security theorem. -/
theorem matches_without_binding (state : State) :
 ∃ (H : Bytes → State) (written current : R9PoolRuntimeBinding.Inputs),
 R9PoolRuntimeBinding.digestMatches H written current ∧
 ¬R9PoolRuntimeBinding.P2Prime H written current := by
 let zero : AspisV8R19.DuplexFrames.Byte:=⟨0,by omega⟩
 let one : AspisV8R19.DuplexFrames.Byte:=⟨1,by omega⟩
 refine ⟨fun _=>state,⟨[zero],[]⟩,⟨[one],[]⟩,⟨rfl,rfl⟩,?_⟩
 intro binding
 have same: [one]=[zero] := (binding ⟨rfl,rfl⟩).1
 have values:=congrArg Fin.val (List.cons.inj same).1
 change 1=0 at values
 omega

#print axioms parsed
#print axioms current
#print axioms by_p2prime
#print axioms matches_without_binding
end NJR_HistoryBinding
