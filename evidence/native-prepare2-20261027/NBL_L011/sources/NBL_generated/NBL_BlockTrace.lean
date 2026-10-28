import NBA_Transcript
import NBA_SamplerValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.NBL_BlockTrace
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
abbrev Bytes32 := Array U8 32#usize
abbrev Log := List (Slice (Slice U8) × Bytes32)

/-- Three ordered native digest observations. The advanced state is derived
from the third reply, not an independently chosen scalar post-state. -/
structure Block {H : Type} (D : aspis_core.Digest32 H)
    (before : transcript.Transcript H) (row : U8) (payload : Slice U8) where
  tag : U8
  tagCall : (160#u8+row : Result U8)=ok tag
  absorbed : Bytes32
  value : Bytes32
  final : Bytes32
  absorbCall : D.digest before.hash (NBA_Transcript.absorbParts before.state tag payload)=ok absorbed
  readCall : D.digest before.hash (NBA_Transcript.readParts absorbed 1#u8)=ok value
  advanceCall : D.digest before.hash (NBA_Transcript.readParts absorbed 2#u8)=ok final

def Block.after {H : Type} {D : aspis_core.Digest32 H}
    {before : transcript.Transcript H} {row : U8} {payload : Slice U8}
    (b : Block D before row payload) : transcript.Transcript H := {before with state:=b.final}

def Block.log {H : Type} {D : aspis_core.Digest32 H}
    {before : transcript.Transcript H} {row : U8} {payload : Slice U8}
    (b : Block D before row payload) : Log :=
  [(NBA_Transcript.absorbParts before.state b.tag payload,b.absorbed),
   (NBA_Transcript.readParts b.absorbed 1#u8,b.value),
   (NBA_Transcript.readParts b.absorbed 2#u8,b.final)]

theorem block_result {H : Type} (D : aspis_core.Digest32 H)
    (before : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (b : Block D before row payload) :
    transcript.Transcript.block D before row payload=ok (b.value,b.after) :=
  NBA_Transcript.block D before row b.tag payload b.absorbed b.value b.final
    b.tagCall b.absorbCall b.readCall b.advanceCall

theorem block_log {H : Type} (D : aspis_core.Digest32 H)
    (before : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (b : Block D before row payload) :
    b.log.length=3 ∧ ∀ event ∈ b.log, D.digest before.hash event.1=ok event.2 := by
  refine ⟨rfl,?_⟩
  intro event member
  simp only [Block.log,List.mem_cons,List.mem_singleton] at member
  rcases member with rfl | rfl | rfl
  · exact b.absorbCall
  · exact b.readCall
  · exact b.advanceCall

/-- Sampling observation is at the SAME block emitted by the digest trace.
Its native sampler association remains a separately discharged child port. -/
structure Scalar {H : Type} (D : aspis_core.Digest32 H)
    (before : transcript.Transcript H) (row : U8) (payload : Slice U8) (nonzero : Bool) where
  block : Block D before row payload
  value : aspis_core.field.WideExact
  sample : (if nonzero then NBA_Installed.actual.sampling.gamma block.value
    else NBA_Installed.actual.sampling.ordinary block.value)=ok value

theorem scalar_result {H : Type} (D : aspis_core.Digest32 H)
    (before : transcript.Transcript H) (row : U8) (payload : Slice U8) (nonzero : Bool)
    (s : Scalar D before row payload nonzero) :
    PreparedModel.scalar NBA_Installed.actual.sampling D before row payload nonzero=
      ok (s.value,s.block.after) :=
  NBA_SamplerValues.scalar D before s.block.after row payload s.block.value s.value nonzero
    (block_result D before row payload s.block) s.sample

#print axioms block_result
#print axioms block_log
#print axioms scalar_result
end AspisR1.NBL_BlockTrace
end
