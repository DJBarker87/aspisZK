import NLP_InputDomain
set_option autoImplicit false
noncomputable section
namespace NLP_InputCounterexample
open Aeneas Aeneas.Std Result AspisR1
open AspisV8R19.SqueezeOracleBridge
attribute [local instance] Classical.propDecidable
abbrev Root := Array U8 32#usize
def zero : Root := Array.repeat 32#usize 0#u8
def one : Root := Array.repeat 32#usize 1#u8
theorem distinct : zero≠one := by
 intro h
 have head:=congrArg (fun r : Root=>r.val.head?) h
 have bad : (0#u8 : U8)=1#u8 := by simpa [zero,one,Array.repeat] using head
 have value:=congrArg (fun x : U8=>x.val) bad
 change 0=1 at value
 omega
def other (root : Root) : Root := if root=zero then one else zero
theorem different (root : Root) : other root≠root := by
 unfold other
 split
 · rename_i equal
   rw [equal]
   exact Ne.symm distinct
 · rename_i different
   exact Ne.symm different
/-- Symbolic list frame law; no recurrence or large numeral is reduced. -/
theorem middle {A : Type} (front mid back : List A) :
 ((front++mid++back).drop front.length).take mid.length=mid := by
 simp [List.append_assoc]
def checkpoint (root : Root) : Slice U8 :=
 ⟨List.replicate 112 0#u8++(other root).val++List.replicate 1624 0#u8,by
  simp only [List.length_append,List.length_replicate,(other root).property]
  scalar_tac⟩
theorem length (root : Root) : (checkpoint root).val.length=1768 := by
 simp only [checkpoint,List.length_append,List.length_replicate,(other root).property]
 rfl
theorem projection (root : Root) : ((checkpoint root).val.drop 112).take 32=(other root).val := by
 have framed:=middle (List.replicate 112 (0#u8 : U8)) (other root).val (List.replicate 1624 (0#u8 : U8))
 simpa only [List.length_replicate,(other root).property,checkpoint] using framed
/-- Length scope alone cannot imply the extra root-provenance relation.
This is an input-domain counterexample ONLY: it asserts no reached C04 or
successful resume, and therefore makes no deployed failure claim. -/
theorem extents_insufficient (proof : Slice U8) :
 ∃ ck : Slice U8,ck.val.length=1768 ∧ ¬NLP_InputDomain.Root0 ck proof := by
 let root : Root:=encodeState ((AspisR1.SemanticRecordCodec.decodeState
  (OraclePortCompactDraft.slice (MultiproofConeCanonical.bytesOf proof.val) 16 32)).getD (fun _=>0))
 refine ⟨checkpoint root,length root,?_⟩
 intro wrong
 change ((checkpoint root).val.drop 112).take 32=root.val at wrong
 rw [projection] at wrong
 exact different root (Subtype.ext wrong)
set_option pp.proofs false
#print distinct
#print different
#print middle
#print length
#print projection
#print extents_insufficient
#print axioms distinct
#print axioms different
#print axioms middle
#print axioms length
#print axioms projection
#print axioms extents_insufficient
end NLP_InputCounterexample
