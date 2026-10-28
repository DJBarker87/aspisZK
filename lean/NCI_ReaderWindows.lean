import NCI_ReaderLayout
import CheckpointBytes3Reader
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCI_ReaderWindows
open Aeneas Aeneas.Std Result
open AspisR1Stage2 MultiproofConeCanonical

theorem weight_step (r : verifier.Reader) (i : Nat)
    (size : r.bytes.val.length = 1768) (cursor : r.at.val = 712 + 16*i) (hi : i < 64) :
    ∃ b : Array U8 16#usize, ∃ out : verifier.Reader,
      b.val = (r.bytes.val.drop r.at.val).take 16 ∧
      out.at.val = 712 + 16*(i+1) ∧ out.bytes = r.bytes ∧
      CheckpointBytes3Reader.readK r = ok
        (CheckpointBytes3Reader.optionK ((ExactLeafFieldCodec.decodeQM31 (bytesOf b.val)).map
          CheckpointBytes3KDecode.rawK),out) := by
  have bound : r.at.val + 16 ≤ r.bytes.val.length := by
    have h := NCI_ReaderLayout.weight_read_bound i hi
    omega
  obtain ⟨b,out,contents,advanced,backing,run⟩ := CheckpointBytes3Reader.read_k_c5 r bound
  exact ⟨b,out,contents,by omega,backing,run⟩

theorem semantic_step (r : verifier.Reader) (i : Nat)
    (size : r.bytes.val.length = 1768) (cursor : r.at.val = 408 + 16*i) (hi : i < 10) :
    ∃ b : Array U8 16#usize, ∃ out : verifier.Reader,
      b.val = (r.bytes.val.drop r.at.val).take 16 ∧
      out.at.val = 408 + 16*(i+1) ∧ out.bytes = r.bytes ∧
      CheckpointBytes3Reader.readK r = ok
        (CheckpointBytes3Reader.optionK ((ExactLeafFieldCodec.decodeQM31 (bytesOf b.val)).map
          CheckpointBytes3KDecode.rawK),out) := by
  have bound : r.at.val + 16 ≤ r.bytes.val.length := by
    have h := NCI_ReaderLayout.semantic_read_bound i hi
    omega
  obtain ⟨b,out,contents,advanced,backing,run⟩ := CheckpointBytes3Reader.read_k_c5 r bound
  exact ⟨b,out,contents,by omega,backing,run⟩
#print axioms weight_step
#print axioms semantic_step
end AspisR1.NCI_ReaderWindows
