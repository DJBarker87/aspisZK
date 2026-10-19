import Aeneas
open Aeneas Aeneas.Std

def chunk0 : List (Std.U32 × Std.U32) := [(0#u32, 0#u32), (1#u32, 1#u32), (2#u32, 2#u32), (3#u32, 3#u32), (4#u32, 4#u32), (5#u32, 5#u32), (6#u32, 6#u32), (7#u32, 7#u32), (8#u32, 8#u32), (9#u32, 9#u32), (10#u32, 10#u32), (11#u32, 11#u32), (12#u32, 12#u32), (13#u32, 13#u32), (14#u32, 14#u32), (15#u32, 15#u32), (16#u32, 16#u32), (17#u32, 17#u32), (18#u32, 18#u32), (19#u32, 19#u32), (20#u32, 20#u32), (21#u32, 21#u32), (22#u32, 22#u32), (23#u32, 23#u32), (24#u32, 24#u32), (25#u32, 25#u32), (26#u32, 26#u32), (27#u32, 27#u32), (28#u32, 28#u32), (29#u32, 29#u32), (30#u32, 30#u32), (31#u32, 31#u32)]
theorem chunk0_length : chunk0.length = 32 := rfl

def chunk1 : List (Std.U32 × Std.U32) := chunk0
theorem chunk1_length : chunk1.length = 32 := by exact chunk0_length

def chunks : List (Std.U32 × Std.U32) := chunk0 ++ chunk1
theorem chunks_length : chunks.length = 64 := by simp [chunks, chunk0_length, chunk1_length]
#print axioms chunk0_length
#print axioms chunks_length
