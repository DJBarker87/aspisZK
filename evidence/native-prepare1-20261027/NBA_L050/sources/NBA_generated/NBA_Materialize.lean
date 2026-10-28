import NBA_Transcript
import NBA_Store8
import NBA_QueryFactor
set_option autoImplicit false
namespace AspisR1.NBA_Materialize
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
abbrev Bytes32 := Array U8 32#usize
theorem source {H : Type} (D : aspis_core.Digest32 H) (hash : H)
    (state b0 a0 b1 a1 b2 a2 b3 a3 b4 a4 b5 a5 b6 a6 b7 a7 : Bytes32)
    (hb0 : D.digest hash (NBA_Transcript.readParts state 1#u8)=ok b0)
    (ha0 : D.digest hash (NBA_Transcript.readParts state 2#u8)=ok a0)
    (hb1 : D.digest hash (NBA_Transcript.readParts a0 1#u8)=ok b1)
    (ha1 : D.digest hash (NBA_Transcript.readParts a0 2#u8)=ok a1)
    (hb2 : D.digest hash (NBA_Transcript.readParts a1 1#u8)=ok b2)
    (ha2 : D.digest hash (NBA_Transcript.readParts a1 2#u8)=ok a2)
    (hb3 : D.digest hash (NBA_Transcript.readParts a2 1#u8)=ok b3)
    (ha3 : D.digest hash (NBA_Transcript.readParts a2 2#u8)=ok a3)
    (hb4 : D.digest hash (NBA_Transcript.readParts a3 1#u8)=ok b4)
    (ha4 : D.digest hash (NBA_Transcript.readParts a3 2#u8)=ok a4)
    (hb5 : D.digest hash (NBA_Transcript.readParts a4 1#u8)=ok b5)
    (ha5 : D.digest hash (NBA_Transcript.readParts a4 2#u8)=ok a5)
    (hb6 : D.digest hash (NBA_Transcript.readParts a5 1#u8)=ok b6)
    (ha6 : D.digest hash (NBA_Transcript.readParts a5 2#u8)=ok a6)
    (hb7 : D.digest hash (NBA_Transcript.readParts a6 1#u8)=ok b7)
    (ha7 : D.digest hash (NBA_Transcript.readParts a6 2#u8)=ok a7)
    : NBA_QueryFactor.materialize D hash state=ok (NBA_Store8.s8 (Array.repeat 32#usize 0#u8) b0 b1 b2 b3 b4 b5 b6 b7,NBA_Store8.s8 (Array.repeat 32#usize 0#u8) a0 a1 a2 a3 a4 a5 a6 a7) := by
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
  unfold NBA_QueryFactor.materialize
  simp only [NBA_Transcript.readParts] at hb0 ha0 hb1 ha1 hb2 ha2 hb3 ha3 hb4 ha4 hb5 ha5 hb6 ha6 hb7 ha7
  simp only [lift,bind_tc_ok]
  rw [hb0,bind_tc_ok,initialRead,bind_tc_ok]
  dsimp! only
  rw [ha0,bind_tc_ok,aw0,ar0,bind_tc_ok]
  rw [hb1,bind_tc_ok,bw0,bw1,bind_tc_ok]
  rw [ha1,bind_tc_ok,aw1,bind_tc_ok,ar1,bind_tc_ok]
  rw [hb2,bind_tc_ok,bw2,bind_tc_ok]
  rw [ha2,bind_tc_ok,aw2,bind_tc_ok,ar2,bind_tc_ok]
  rw [hb3,bind_tc_ok,bw3,bind_tc_ok]
  rw [ha3,bind_tc_ok,aw3,bind_tc_ok,ar3,bind_tc_ok]
  rw [hb4,bind_tc_ok,bw4,bind_tc_ok]
  rw [ha4,bind_tc_ok,aw4,bind_tc_ok,ar4,bind_tc_ok]
  rw [hb5,bind_tc_ok,bw5,bind_tc_ok]
  rw [ha5,bind_tc_ok,aw5,bind_tc_ok,ar5,bind_tc_ok]
  rw [hb6,bind_tc_ok,bw6,bind_tc_ok]
  rw [ha6,bind_tc_ok,aw6,bind_tc_ok,ar6,bind_tc_ok]
  rw [hb7,bind_tc_ok,bw7,bind_tc_ok]
  rw [ha7,bind_tc_ok,aw7,bind_tc_ok,ar7,bind_tc_ok]

#print axioms source
end AspisR1.NBA_Materialize
