import RawJ_DigestRead
import S1SemanticCodeSampleBlockV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawJ_SampleRead
open Aeneas Aeneas.Std Result FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode AuS1_Suffix
open MultiproofConeCanonical

def parts (state : Array U8 32#usize) (tag : U8) (framed : Slice U8) : Slice (Slice U8) :=
  Array.to_slice (Array.make 3#usize [Array.to_slice state,
    Array.to_slice (Array.make 2#usize [0#u8,tag]),framed])

theorem frame {H : Type} (D : aspis_core.Digest32 H) (self after : r1_wire.SemanticTranscript H)
    (row : U8) (framed : Slice U8) (out : Array U8 32#usize)
    (success : erase (S1SemanticCode.sampleBlock D self row framed) = ok (.Ok out,after)) :
    ∃ tag, (160#u8+row : Result U8) = ok tag ∧
      Read (observe (run (S1SemanticCode.sampleBlock D self row framed)).1)
        (flatten (parts self.state tag framed)) := by
  let log := observe (run (S1SemanticCode.sampleBlock D self row framed)).1
  have inc : ∀ frame, Read (observe (run (S1SemanticCode.sampleBlock D self row framed)).1) frame →
      Read log frame := fun _ h => h
  change ∃ tag, _ ∧ Read log _
  unfold S1SemanticCode.sampleBlock at success inc
  split at success
  · cases success
  · rename_i branch
    simp only [if_neg branch] at inc
    obtain ⟨s,hs,s1,sub1⟩ := right_read _ _ _ success
    obtain ⟨tag,htag,s2,sub2⟩ := right_read _ _ _ s1
    rw [erase_lift] at hs htag
    have same : s = Array.to_slice self.state := (Result.ok.inj hs).symm
    subst s
    obtain ⟨s1,hs1,s3,sub3⟩ := right_read _ _ _ s2
    obtain ⟨s2,hs2,s4,sub4⟩ := right_read _ _ _ s3
    rw [erase_lift] at hs1 hs2
    cases Result.ok.inj hs1
    cases Result.ok.inj hs2
    obtain ⟨absorbed,digest,s5,sub5⟩ := right_read _ _ _ s4
    refine ⟨tag,htag,?_⟩
    have member := left_read _ _ _ s4 _ (RawJ_DigestRead.digest D self.hash _ absorbed digest)
    exact inc _ (sub1 _ (sub2 _ (sub3 _ (sub4 _ member))))

theorem target (state : Array U8 32#usize) (tag : U8) (framed : Slice U8)
    (root : Array U8 32#usize) (pre : List U8) (shape : framed.val = pre ++ root.val) :
    BinRawByteCollisionTargets.pred 2 (flatten (parts state tag framed)) = some (decodeState root) := by
  rw [BinRawByteCollisionTargets.pred_tail]
  have same : flatten (parts state tag framed) =
      (bytesOf state.val ++ [decodeByte 0#u8,decodeByte tag] ++ bytesOf pre) ++ bytes (decodeState root) := by
    simp only [parts,flatten,Array.to_slice,Array.make,List.flatMap_cons,List.flatMap_nil,shape,
      bytesOf,List.map_append,List.map_cons,List.map_nil,List.append_nil,
      MultiproofConePhysicalTransport.digest_bytes,List.append_assoc]
  rw [same]
  exact BinRawByteCollisionTargets.trailing_frame _ _

#print axioms frame
#print axioms target
end AspisR1.RawJ_SampleRead
end
