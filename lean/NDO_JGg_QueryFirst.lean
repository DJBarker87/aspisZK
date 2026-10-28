import NDO_JGg_QuerySplit
import NDO_JGg_QueryArrays
set_option autoImplicit false
namespace AspisR1.JGg_QueryFirst
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.SqueezeOracleBridge JGg_QuerySplit
attribute [local irreducible] later

theorem source {Hash A : Type} (D : aspis_core.Digest32 Hash)
    (self absorbed : transcript.Transcript Hash) (row : U8) (payload : Slice U8)
    (block next : Bytes32)
    (absorb : transcript.Transcript.absorb D self row payload=ok absorbed)
    (read : D.digest absorbed.hash (TranscriptStep.readParts absorbed.state 1#u8)=ok block)
    (advance : D.digest absorbed.hash (TranscriptStep.readParts absorbed.state 2#u8)=ok next)
    (k : transcript.Transcript Hash → Blocks → Blocks → Result A) :
    initial D self row payload k=
    later D absorbed.hash (JGg_QueryArrays.back block) (JGg_QueryArrays.back next) next (k absorbed) := by
  unfold initial
  rw [absorb,bind_tc_ok,read,bind_tc_ok]
  erw [JGg_QueryArrays.mutable,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [advance,bind_tc_ok]
  have index : Array.index_usize (JGg_QueryArrays.back next) 0#usize=ok next := rfl
  erw [index,bind_tc_ok]
#print axioms source
end AspisR1.JGg_QueryFirst
