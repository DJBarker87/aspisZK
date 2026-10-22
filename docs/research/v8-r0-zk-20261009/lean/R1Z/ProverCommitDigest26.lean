import R1Z.ProverCommitQueryTotal26
import R1Z.ProverCommitSemanticTransport26
import R1Z.ProverCommitProductOracle25
import R1Z.ProverCommitOwnedBackend
import R1Z.ProverCommitStreamBytes
/-! Concrete shared-oracle instances for all three extracted Digest32 owners.
Input slices are concatenated in source order; output bytes use the retained
owned sampler representation. This is a ROM interpretation, not a claim that
a native digest implements a random oracle. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitDigest26
open Aeneas Aeneas.Std Result
open R0Z R0Z.FsStatement R0Z.LawTransport
open R1Z.ProverCommitProductOracle25
abbrev Oracle := List UInt8 → OracleAnswer
abbrev Parts := Slice (Slice U8)
abbrev Bytes32 := Array U8 32#usize
private def answerFinite : Fintype OracleAnswer := inferInstance
attribute [local instance] answerFinite
attribute [local irreducible] answerFinite
private def inputFinite : Fintype Input := inferInstance
attribute [local instance] inputFinite
attribute [local irreducible] inputFinite

def read (oracle : Oracle) (parts : Parts) : Result Bytes32 :=
  ok (ProverCommitOwnedDecoder.answerBytes (oracle (ProverCommitStreamBytes.wireBytes parts)))

def semantic : AspisR1SimSemantic20.aspis_core.digest.Digest32 Oracle :=
  ⟨BuiltinCopy _,read⟩
def circle : AspisR1CircleCaller25.aspis_core.digest.Digest32 Oracle :=
  ⟨BuiltinCopy _,read⟩
def control : AspisR1SimControl21.aspis_core.digest.Digest32 Oracle :=
  ⟨BuiltinCopy _,read⟩

theorem semantic_circle : ProverCommitCircle25.fromHash semantic = circle := rfl

theorem total (oracle : Oracle) (parts : Parts) :
    semantic.digest oracle parts = ok (ProverCommitOwnedDecoder.answerBytes
      (oracle (ProverCommitStreamBytes.wireBytes parts))) ∧
    circle.digest oracle parts = ok (ProverCommitOwnedDecoder.answerBytes
      (oracle (ProverCommitStreamBytes.wireBytes parts))) ∧
    control.digest oracle parts = ok (ProverCommitOwnedDecoder.answerBytes
      (oracle (ProverCommitStreamBytes.wireBytes parts))) := ⟨rfl,rfl,rfl⟩

def productOracle (bound : Nat) (fits : 65≤bound) (seed : OracleAnswer)
    (p : Input × (RomFiniteBin.Address bound → OracleAnswer)) : Oracle :=
  RomFiniteBin.lookup bound (table bound fits seed p)

/-- The installed source digest reads the actual packed stream-3 coordinate.
The hypothesis is an address equality, not an output or execution premise. -/
theorem packed_read (bound : Nat) (fits : 65≤bound) (seed : OracleAnswer)
    (p : Input × (RomFiniteBin.Address bound → OracleAnswer)) (i : Coord) (parts : Parts)
    (address : ProverCommitStreamBytes.wireBytes parts = (key bound fits seed i).val) :
    semantic.digest (productOracle bound fits seed p) parts =
      ok (ProverCommitOwnedDecoder.answerBytes (words p.1 i)) := by
  simp only [semantic,read,productOracle,address,RomFiniteBin.lookup,
    RomFiniteBin.decode_encode,source_at]

/-- The entire installed digest function has the exact source-table law.
It covers any consumer of these extracted APIs, including repeated calls;
it does not identify a model continuation with a source continuation. -/
theorem digest_law (bound : Nat) [Fintype (RomFiniteBin.Address bound)]
    (fits : 65≤bound) (seed : OracleAnswer)
    (test : (Parts → Result Bytes32) → ℚ) :
    mean (fun p => test (semantic.digest (productOracle bound fits seed p))) =
      mean (fun t : RomFiniteBin.Address bound → OracleAnswer =>
        test (semantic.digest (RomFiniteBin.lookup bound t))) := by
  exact (QueryScanIdealHistory.mean_fintype_transport _ _ _).trans
    ((source_oracle_uniform bound fits seed
      (fun t => test (semantic.digest (RomFiniteBin.lookup bound t)))).trans
        (QueryScanIdealHistory.mean_fintype_transport _ _ _))

#print axioms semantic_circle
#print axioms total
#print axioms packed_read
#print axioms digest_law
end R1Z.ProverCommitDigest26
