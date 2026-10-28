import NDO_JGg_QuerySplit
set_option autoImplicit false
namespace AspisR1.JGg_QueryStep
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.SqueezeOracleBridge JGg_QuerySplit

theorem source {Hash A : Type} (D : aspis_core.Digest32 Hash) (hash : Hash)
    (i : Usize) (state block next : Bytes32) (b a b1 a1 : Blocks)
    (read : D.digest hash (TranscriptStep.readParts state 1#u8)=ok block)
    (advance : D.digest hash (TranscriptStep.readParts state 2#u8)=ok next)
    (bu : Array.update b i block=ok b1) (au : Array.update a i next=ok a1)
    (selected : Array.index_usize a1 i=ok next)
    (k : Blocks → Blocks → Bytes32 → Result A) :
    step D hash i state b a k=k b1 a1 next := by
  unfold step
  rw [read,bind_tc_ok,bu,bind_tc_ok,advance,bind_tc_ok,au,bind_tc_ok,selected,bind_tc_ok]
#print axioms source
end AspisR1.JGg_QueryStep
