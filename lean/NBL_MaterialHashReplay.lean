import NBL_RunStep
import NBL_QueryEffectFactor
import NBL_HashReplay
import NBL_MaterialTrace
set_option autoImplicit false
namespace AspisR1.NBL_MaterialHashReplay
open Aeneas Aeneas.Std Result AspisR1PublicPreparation PreparedHashCode NBL_CodeRunLaws

def log {H : Type} {D : aspis_core.Digest32 H} {hash : H} {before : NBL_MaterialTrace.Bytes32}
    (t : NBL_MaterialTrace.Trace D hash before) : NBL_BlockTrace.Log :=
  [
    (NBA_Transcript.readParts before 1#u8,t.p0.block),
    (NBA_Transcript.readParts before 2#u8,t.p0.advance),
    (NBA_Transcript.readParts t.p0.advance 1#u8,t.p1.block),
    (NBA_Transcript.readParts t.p0.advance 2#u8,t.p1.advance),
    (NBA_Transcript.readParts t.p1.advance 1#u8,t.p2.block),
    (NBA_Transcript.readParts t.p1.advance 2#u8,t.p2.advance),
    (NBA_Transcript.readParts t.p2.advance 1#u8,t.p3.block),
    (NBA_Transcript.readParts t.p2.advance 2#u8,t.p3.advance),
    (NBA_Transcript.readParts t.p3.advance 1#u8,t.p4.block),
    (NBA_Transcript.readParts t.p3.advance 2#u8,t.p4.advance),
    (NBA_Transcript.readParts t.p4.advance 1#u8,t.p5.block),
    (NBA_Transcript.readParts t.p4.advance 2#u8,t.p5.advance),
    (NBA_Transcript.readParts t.p5.advance 1#u8,t.p6.block),
    (NBA_Transcript.readParts t.p5.advance 2#u8,t.p6.advance),
    (NBA_Transcript.readParts t.p6.advance 1#u8,t.p7.block),
    (NBA_Transcript.readParts t.p6.advance 2#u8,t.p7.advance)]

theorem source {H : Type} (D : aspis_core.Digest32 H) (hash : H) (before : NBL_MaterialTrace.Bytes32)
    (t : NBL_MaterialTrace.Trace D hash before) :
    run (NBL_QueryEffectFactor.materialize D hash before)=
      (NBL_HashReplay.events D hash (log t),ok (t.blocks,t.advances)) := by
  let b0 := t.p0.block
  let a0 := t.p0.advance
  let b1 := t.p1.block
  let a1 := t.p1.advance
  let b2 := t.p2.block
  let a2 := t.p2.advance
  let b3 := t.p3.block
  let a3 := t.p3.advance
  let b4 := t.p4.block
  let a4 := t.p4.advance
  let b5 := t.p5.block
  let a5 := t.p5.advance
  let b6 := t.p6.block
  let a6 := t.p6.advance
  let b7 := t.p7.block
  let a7 := t.p7.advance
  have hb0 := t.p0.readCall
  have ha0 := t.p0.advanceCall
  have hb1 := t.p1.readCall
  have ha1 := t.p1.advanceCall
  have hb2 := t.p2.readCall
  have ha2 := t.p2.advanceCall
  have hb3 := t.p3.readCall
  have ha3 := t.p3.advanceCall
  have hb4 := t.p4.readCall
  have ha4 := t.p4.advanceCall
  have hb5 := t.p5.readCall
  have ha5 := t.p5.advanceCall
  have hb6 := t.p6.readCall
  have ha6 := t.p6.advanceCall
  have hb7 := t.p7.readCall
  have ha7 := t.p7.advanceCall
  have bw0 := NBA_Store8.write0 (Array.repeat 32#usize 0#u8) b0 b1 b2 b3 b4 b5 b6 b7
  have bw1 := NBA_Store8.write1 (Array.repeat 32#usize 0#u8) b0 b1 b2 b3 b4 b5 b6 b7
  have bw2 := NBA_Store8.write2 (Array.repeat 32#usize 0#u8) b0 b1 b2 b3 b4 b5 b6 b7
  have bw3 := NBA_Store8.write3 (Array.repeat 32#usize 0#u8) b0 b1 b2 b3 b4 b5 b6 b7
  have bw4 := NBA_Store8.write4 (Array.repeat 32#usize 0#u8) b0 b1 b2 b3 b4 b5 b6 b7
  have bw5 := NBA_Store8.write5 (Array.repeat 32#usize 0#u8) b0 b1 b2 b3 b4 b5 b6 b7
  have bw6 := NBA_Store8.write6 (Array.repeat 32#usize 0#u8) b0 b1 b2 b3 b4 b5 b6 b7
  have bw7 := NBA_Store8.write7 (Array.repeat 32#usize 0#u8) b0 b1 b2 b3 b4 b5 b6 b7
  have br0 := NBA_Store8.read0 (Array.repeat 32#usize 0#u8) b0 b1 b2 b3 b4 b5 b6 b7
  have br1 := NBA_Store8.read1 (Array.repeat 32#usize 0#u8) b0 b1 b2 b3 b4 b5 b6 b7
  have br2 := NBA_Store8.read2 (Array.repeat 32#usize 0#u8) b0 b1 b2 b3 b4 b5 b6 b7
  have br3 := NBA_Store8.read3 (Array.repeat 32#usize 0#u8) b0 b1 b2 b3 b4 b5 b6 b7
  have br4 := NBA_Store8.read4 (Array.repeat 32#usize 0#u8) b0 b1 b2 b3 b4 b5 b6 b7
  have br5 := NBA_Store8.read5 (Array.repeat 32#usize 0#u8) b0 b1 b2 b3 b4 b5 b6 b7
  have br6 := NBA_Store8.read6 (Array.repeat 32#usize 0#u8) b0 b1 b2 b3 b4 b5 b6 b7
  have br7 := NBA_Store8.read7 (Array.repeat 32#usize 0#u8) b0 b1 b2 b3 b4 b5 b6 b7
  have aw0 : NBA_Store8.back (Array.repeat 32#usize 0#u8) b0 b1 b2 b3 b4 b5 b6 b7 a0=NBA_Store8.s1 (Array.repeat 32#usize 0#u8) a0 a1 a2 a3 a4 a5 a6 a7 := by rfl
  have aw1 := NBA_Store8.write1 (Array.repeat 32#usize 0#u8) a0 a1 a2 a3 a4 a5 a6 a7
  have aw2 := NBA_Store8.write2 (Array.repeat 32#usize 0#u8) a0 a1 a2 a3 a4 a5 a6 a7
  have aw3 := NBA_Store8.write3 (Array.repeat 32#usize 0#u8) a0 a1 a2 a3 a4 a5 a6 a7
  have aw4 := NBA_Store8.write4 (Array.repeat 32#usize 0#u8) a0 a1 a2 a3 a4 a5 a6 a7
  have aw5 := NBA_Store8.write5 (Array.repeat 32#usize 0#u8) a0 a1 a2 a3 a4 a5 a6 a7
  have aw6 := NBA_Store8.write6 (Array.repeat 32#usize 0#u8) a0 a1 a2 a3 a4 a5 a6 a7
  have aw7 := NBA_Store8.write7 (Array.repeat 32#usize 0#u8) a0 a1 a2 a3 a4 a5 a6 a7
  have ar0 := NBA_Store8.read0 (Array.repeat 32#usize 0#u8) a0 a1 a2 a3 a4 a5 a6 a7
  have ar1 := NBA_Store8.read1 (Array.repeat 32#usize 0#u8) a0 a1 a2 a3 a4 a5 a6 a7
  have ar2 := NBA_Store8.read2 (Array.repeat 32#usize 0#u8) a0 a1 a2 a3 a4 a5 a6 a7
  have ar3 := NBA_Store8.read3 (Array.repeat 32#usize 0#u8) a0 a1 a2 a3 a4 a5 a6 a7
  have ar4 := NBA_Store8.read4 (Array.repeat 32#usize 0#u8) a0 a1 a2 a3 a4 a5 a6 a7
  have ar5 := NBA_Store8.read5 (Array.repeat 32#usize 0#u8) a0 a1 a2 a3 a4 a5 a6 a7
  have ar6 := NBA_Store8.read6 (Array.repeat 32#usize 0#u8) a0 a1 a2 a3 a4 a5 a6 a7
  have ar7 := NBA_Store8.read7 (Array.repeat 32#usize 0#u8) a0 a1 a2 a3 a4 a5 a6 a7
  have initialRead : Array.index_mut_usize (Array.repeat 8#usize (Array.repeat 32#usize 0#u8)) 0#usize=ok (Array.repeat 32#usize 0#u8,NBA_Store8.back (Array.repeat 32#usize 0#u8) b0 b1 b2 b3 b4 b5 b6 b7) := by rfl

  simp only [NBA_Transcript.readParts] at hb0 ha0 hb1 ha1 hb2 ha2 hb3 ha3 hb4 ha4 hb5 ha5 hb6 ha6 hb7 ha7
  unfold NBL_QueryEffectFactor.materialize
  simp only [NBL_HashReplay.events,log,List.map_cons,List.map_nil]
  repeat' first
    | (apply NBL_RunStep.lift_ok; first | assumption | rfl)
    | (apply NBL_RunStep.digest_ok; assumption)
    | (rw [aw0])
    | exact pure_run _

#print axioms source
end AspisR1.NBL_MaterialHashReplay
