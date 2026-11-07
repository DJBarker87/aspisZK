import RSL_TX2_217
set_option autoImplicit false
namespace NMX_R3_LaneModels
open RSL

def emit (b : Bytes) (master : B32) (lane : UInt8) (next : UInt64)
 (root : Digest) (frontier : List Digest) : Option LaneState :=
 if next == 0 && root != EMPTY_ROOTS.getD TREE_DEPTH [] then none else
 some ⟨b.getD 72 0, master, lane, ⟨next,root,frontier⟩⟩

def frontier (b : Bytes) (master : B32) (lane : UInt8) (t : Bytes)
 (next : UInt64) (root : Digest) : Option LaneState :=
 match TX2_217.frontierLoop t next TREE_DEPTH with
 | none => none
 | some f => emit b master lane next root f

def digest (b : Bytes) (master : B32) (lane : UInt8) (t : Bytes) (next : UInt64) : Option LaneState :=
 match TX2_217.decodeDigestCanonical (slice t 16 48) with
 | none => none
 | some root => frontier b master lane t next root

def counter (b : Bytes) (master : B32) (lane : UInt8) (t : Bytes) : Option LaneState :=
 let next := le64 (slice t 8 16)
 if decide (PAIR_CAPACITY < next) then none else digest b master lane t next

def tree (b : Bytes) (master : B32) (lane : UInt8) : Option LaneState :=
 let t := b.drop LANE_HEADER_BYTES
 if TX2_217.treeHeaderBad t then none else counter b master lane t

def master (b : Bytes) (lane : UInt8) : Option LaneState :=
 let mb := slice b 40 72
 if mb.all (· == 0) then none else
 if h : mb.length = 32 then tree b ⟨mb,h⟩ lane else none

def header (b : Bytes) : Option LaneState :=
 if TX2_217.headerBad b then none else master b (b.getD 5 0)
end NMX_R3_LaneModels
