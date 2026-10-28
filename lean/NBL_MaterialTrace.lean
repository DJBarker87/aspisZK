import NBA_Materialize
import NBL_BlockTrace
set_option autoImplicit false
namespace AspisR1.NBL_MaterialTrace
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
abbrev Bytes32 := Array U8 32#usize

structure Pair {H : Type} (D : aspis_core.Digest32 H) (hash : H) (before : Bytes32) where
  block : Bytes32
  advance : Bytes32
  readCall : D.digest hash (NBA_Transcript.readParts before 1#u8)=ok block
  advanceCall : D.digest hash (NBA_Transcript.readParts before 2#u8)=ok advance

structure Trace {H : Type} (D : aspis_core.Digest32 H) (hash : H) (before : Bytes32) where
  p0 : Pair D hash before
  p1 : Pair D hash p0.advance
  p2 : Pair D hash p1.advance
  p3 : Pair D hash p2.advance
  p4 : Pair D hash p3.advance
  p5 : Pair D hash p4.advance
  p6 : Pair D hash p5.advance
  p7 : Pair D hash p6.advance

def Trace.blocks {H : Type} {D : aspis_core.Digest32 H} {hash : H} {before : Bytes32}
    (t : Trace D hash before) : Array Bytes32 8#usize :=
  NBA_Store8.s8 (Array.repeat 32#usize 0#u8) t.p0.block t.p1.block t.p2.block t.p3.block
    t.p4.block t.p5.block t.p6.block t.p7.block

def Trace.advances {H : Type} {D : aspis_core.Digest32 H} {hash : H} {before : Bytes32}
    (t : Trace D hash before) : Array Bytes32 8#usize :=
  NBA_Store8.s8 (Array.repeat 32#usize 0#u8) t.p0.advance t.p1.advance t.p2.advance t.p3.advance
    t.p4.advance t.p5.advance t.p6.advance t.p7.advance

/-- All eight eager pairs use a single chronological state carrier. -/
theorem source {H : Type} (D : aspis_core.Digest32 H) (hash : H) (before : Bytes32)
    (t : Trace D hash before) : NBA_QueryFactor.materialize D hash before=ok (t.blocks,t.advances) :=
  NBA_Materialize.source D hash before
    t.p0.block t.p0.advance t.p1.block t.p1.advance t.p2.block t.p2.advance t.p3.block t.p3.advance
    t.p4.block t.p4.advance t.p5.block t.p5.advance t.p6.block t.p6.advance t.p7.block t.p7.advance
    t.p0.readCall t.p0.advanceCall t.p1.readCall t.p1.advanceCall t.p2.readCall t.p2.advanceCall
    t.p3.readCall t.p3.advanceCall t.p4.readCall t.p4.advanceCall t.p5.readCall t.p5.advanceCall
    t.p6.readCall t.p6.advanceCall t.p7.readCall t.p7.advanceCall

#print axioms source
end AspisR1.NBL_MaterialTrace
