import OracleDecisionDomSepSourceFrames
import OracleDecisionMultiDecoderDepth

/-! The frozen node grammar is faithfully modelled and public-init separated,
yet the CURRENT causal decoder recognises one such input as a semantic
absorb. This blocks the requested universal zero-start shortcut, not an
alternative aggregate Q+34 charging argument. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OracleDecisionDomSepDecoderObstruction
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open OracleDecisionMultiTree

abbrev selectedChildren := children OracleDecisionMultiDecoder.zero OracleDecisionMultiDecoder.right

theorem frozen_node_eq : OracleDecisionDomSepFrozen.node selectedChildren =
    OracleDecisionMultiDecoder.node :=
  (OracleDecisionDomSepFrozen.path_node_refines selectedChildren).symm

/-- Exact overlap is with row-one absorb, not with public initialization. -/
theorem frozen_node_absorb : OracleDecisionDomSepFrozen.node selectedChildren =
    bytes OracleDecisionMultiDecoder.endpoint ++ [0, 161] ++ List.replicate 31 0 := by
  rw [frozen_node_eq]
  exact OracleDecisionMultiDecoder.node_absorb

theorem frozen_node_recognized :
    RecordedBinaryExperimentBin.dec (OracleDecisionDomSepFrozen.node selectedChildren)
      OracleDecisionMultiDecoder.table ≠ none := by
  rw [frozen_node_eq]
  exact OracleDecisionMultiDecoder.recognized_node

/-- The very same byte input lies outside the frozen source-frame envelope. -/
theorem recognized_outside_source_frames :
    ¬ OracleDecisionDomSepSourceFrames.SourceFrameEnvelope
      (OracleDecisionDomSepFrozen.node selectedChildren) ∧
    RecordedBinaryExperimentBin.dec (OracleDecisionDomSepFrozen.node selectedChildren)
      OracleDecisionMultiDecoder.table ≠ none :=
  ⟨OracleDecisionDomSepSourceFrames.node_excluded selectedChildren, frozen_node_recognized⟩

/-- A leading node tag cannot separate an absorb grammar with an arbitrary
32-byte state prefix: the tag is simply the first state byte. -/
theorem leading_tag_overlap (tag : Byte) :
    tag :: (List.replicate 32 (0 : Byte) ++ (161 :: List.replicate 31 0)) =
      (tag :: List.replicate 31 0) ++ [0, 161] ++ List.replicate 31 0 := by
  rfl

/-- Verbatim universal rejection target is false for the existing decoder. -/
theorem no_universal_frozen_node_rejection :
    ¬ (∀ (cs : BinMerkle32Path.Children) (T : Table Bytes State),
      RecordedBinaryExperimentBin.dec (OracleDecisionDomSepFrozen.node cs) T = none) := by
  intro h
  exact frozen_node_recognized (h selectedChildren OracleDecisionMultiDecoder.table)

/-- Preserve the existing completely instantiated depth-18 example. Its
upper padding uses a colliding oracle; no accepted frozen-run claim follows. -/
theorem frozen_depth18_start :
    OracleDecisionDomSepFrozen.node selectedChildren = OracleDecisionMultiDecoder.node ∧
    DecodedFirstReadUnionBound.decoderFirstReads RecordedBinaryExperimentBin.dec
      OracleDecisionMultiDecoder.table
      (eval OracleDecisionMultiDecoderDepth.exampleHash
        (terminal [⟨OracleDecisionMultiDecoderDepth.pad 17 OracleDecisionMultiDecoder.exampleTree,
          OracleDecisionMultiDecoderDepth.five⟩] [] [])).1 = 1 :=
  ⟨frozen_node_eq, OracleDecisionMultiDecoderDepth.concrete_depth18_count⟩

#print axioms frozen_node_eq
#print axioms frozen_node_absorb
#print axioms frozen_node_recognized
#print axioms recognized_outside_source_frames
#print axioms leading_tag_overlap
#print axioms no_universal_frozen_node_rejection
#print axioms frozen_depth18_start
end AspisR1.OracleDecisionDomSepDecoderObstruction
end
