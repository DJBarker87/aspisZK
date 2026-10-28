import NCD_KMX_CopyMeaning
import NCD_ChronologicalQuery
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCD_QueryFrame
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
abbrev Bytes32 := Array U8 32#usize
/-- Full value ports for the two native eight-block arrays and local state.
Only indices0..7 have a native array readback. Allocation validity is P6. -/
structure Carrier where
  blocks : Nat → Bytes32
  advances : Nat → Bytes32
  state : Bytes32

def step (before : Carrier) (i : Nat) (block advance : Bytes32) : Carrier :=
  ⟨KMX_CopyMeaning.write before.blocks i block,
   KMX_CopyMeaning.write before.advances i advance,
   if i<7 then advance else before.state⟩

/-- Ordered local write/frame observations of the SAME two full carriers.
No whole materialization output equality is a premise. -/
inductive Trace (reply : Nat → Bytes32) : Nat → Nat → Carrier → Carrier → Prop
  | done (start : Nat) (before : Carrier) (bound : start≤8) : Trace reply start 0 before before
  | more (start count : Nat) (before after final : Carrier)
      (active : start<8)
      (input : before.state=reply (2*start))
      (writes : after=step before start (reply (2*start+1)) (reply (2*start+2)))
      (tail : Trace reply (start+1) count after final) :
      Trace reply start (count+1) before final

theorem blocks {reply : Nat → Bytes32} {start count : Nat} {before final : Carrier}
    (trace : Trace reply start count before final) :
    final.blocks=KMX_CopyMeaning.loop (fun i => reply (2*i+1)) before.blocks start count := by
  induction trace with
  | done => rfl
  | more start count before after final active input writes tail ih =>
    subst after
    simpa only [KMX_CopyMeaning.loop,step] using ih

theorem advances {reply : Nat → Bytes32} {start count : Nat} {before final : Carrier}
    (trace : Trace reply start count before final) :
    final.advances=KMX_CopyMeaning.loop (fun i => reply (2*i+2)) before.advances start count := by
  induction trace with
  | done => rfl
  | more start count before after final active input writes tail ih =>
    subst after
    simpa only [KMX_CopyMeaning.loop,step] using ih

theorem readback {reply : Nat → Bytes32} {before final : Carrier}
    (trace : Trace reply 0 8 before final) (i : Nat) (inside : i<8) :
    final.blocks i=reply (2*i+1) ∧ final.advances i=reply (2*i+2) := by
  rw [blocks trace,advances trace]
  simp only [KMX_CopyMeaning.copy_prefix,if_pos inside]

def encode (f : Nat → Bytes32) : Array Bytes32 8#usize :=
  ⟨List.ofFn (fun i : Fin 8 => f i.val),by simp⟩

theorem materialized {Hash : Type} (H : Bytes → State) (D : aspis_core.Digest32 Hash)
    (hash : Hash) (reply : Nat → Bytes32) (before final : Carrier)
    (trace : Trace reply 0 8 before final)
    (reads : ∀ i, i<8 → decodeState (reply (2*i+1))=
      H (flatten (NBA_Transcript.readParts (reply (2*i)) 1#u8)))
    (advanceValues : ∀ i, i<8 → decodeState (reply (2*i+2))=
      H (flatten (NBA_Transcript.readParts (reply (2*i)) 2#u8))) :
    NBA_QueryFactor.materialize (F3U_Rehash.dictionary H D) hash (reply 0)=
      ok (encode final.blocks,encode final.advances) := by
  let paired := NCD_ChronologicalQuery.pairs H D hash reply reads advanceValues
  have call := NBL_MaterialTrace.source _ hash (reply 0) paired
  have blockValues (i : Fin 8) :
      (paired.blocks.val[i.val]'(by rw [paired.blocks.property];exact i.isLt))=reply (2*i.val+1) := by
    fin_cases i <;> rfl
  have advanceRead (i : Fin 8) :
      (paired.advances.val[i.val]'(by rw [paired.advances.property];exact i.isLt))=reply (2*i.val+2) := by
    fin_cases i <;> rfl
  have blockSame : paired.blocks=encode final.blocks := by
    apply Subtype.ext
    apply List.ext_getElem
    · simp only [encode,List.length_ofFn,paired.blocks.property];rfl
    · intro i hi hj
      have small : i<8 := by rw [paired.blocks.property] at hi;exact hi
      rw [blockValues ⟨i,small⟩]
      simp only [encode,List.getElem_ofFn]
      exact (readback trace i small).1.symm
  have advanceSame : paired.advances=encode final.advances := by
    apply Subtype.ext
    apply List.ext_getElem
    · simp only [encode,List.length_ofFn,paired.advances.property];rfl
    · intro i hi hj
      have small : i<8 := by rw [paired.advances.property] at hi;exact hi
      rw [advanceRead ⟨i,small⟩]
      simp only [encode,List.getElem_ofFn]
      exact (readback trace i small).2.symm
  rw [blockSame,advanceSame] at call
  exact call
#print axioms blocks
#print axioms advances
#print axioms readback
#print axioms materialized
end AspisR1.NCD_QueryFrame
end
