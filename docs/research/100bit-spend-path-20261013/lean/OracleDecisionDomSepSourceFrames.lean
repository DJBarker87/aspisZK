import OracleDecisionDomSepFrozen

/-! A conservative length envelope for the selected frozen S2 transcript
calls. Membership is not a causal-decoder recognition theorem. The envelope
allows every byte string of each listed length, so exclusion is stronger
than checking the record payloads individually. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OracleDecisionDomSepSourceFrames
open FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionDomSepFrozen

/-- Squeeze/advance; opening absorbs; semantic absorbs; opening reseed.
Public initialization has a variable length and is handled separately. -/
def nonInitLengths : List Nat :=
  [33, 38, 39, 62, 70, 71, 262, 294, 935, 966, 967, 2086, 3751]

def SourceFrameEnvelope (b : Bytes) : Prop :=
  (∃ pub root, b = initial pub root) ∨ b.length ∈ nonInitLengths

theorem node_excluded (cs : BinMerkle32Path.Children) :
    ¬ SourceFrameEnvelope (node cs) := by
  rintro (⟨pub, root, h⟩ | h)
  · exact node_not_initial cs pub root h
  · have hn : (node cs).length = 65 := by
      rw [← path_node_refines]; exact BinMerkle32Path.nodeInput_length cs
    rw [hn] at h
    simp [nonInitLengths] at h

theorem leaf_excluded (tag : Byte) (packed salt : Bytes)
    (hp : packed.length = 480 ∨ packed.length = 128) (hs : salt.length = 32) :
    ¬ SourceFrameEnvelope (leaf tag packed salt) := by
  rintro (⟨pub, root, h⟩ | h)
  · exact leaf_not_initial tag packed salt pub root h
  · have hl : (leaf tag packed salt).length = packed.length + 34 := by
      simp [leaf, hs]
    rw [hl] at h
    rcases hp with hp | hp <;> rw [hp] at h <;> simp [nonInitLengths] at h

#print axioms node_excluded
#print axioms leaf_excluded
end AspisR1.OracleDecisionDomSepSourceFrames
end
