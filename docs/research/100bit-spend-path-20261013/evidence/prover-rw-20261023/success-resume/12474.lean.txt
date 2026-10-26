import R1Z.ProverRwOrderedOracle
import R1Z.ProverRwQueryMaterial
set_option autoImplicit false
namespace R1Z.ProverRwOrderedQuerySource
open Aeneas Aeneas.Std Result ProverRwFull ProverRwQueryScan
open ProverRwOrderedOracle
variable [ExternalTypes] [ExternalFuns]
def absorb
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8)
  :
  Execution (host_transcript.Transcript H)
  := do
  let s ← native (Aeneas.Std.lift (Array.to_slice self.state))
  let i ← native (Aeneas.Std.lift (Std.U8.wrapping_add 160#u8 row))
  let s1 ← native (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ 0#u8, i ])))
  let i1 := Slice.len payload
  let i2 ← native (Aeneas.Std.lift (UScalar.cast .U32 i1))
  let a ← native (Aeneas.Std.lift (core.num.U32.to_le_bytes i2))
  let s2 ← native (Aeneas.Std.lift (Array.to_slice a))
  let s3 ← native (Aeneas.Std.lift (Array.to_slice (Array.make 4#usize [ s, s1, s2, payload ])))
  let a1 ← query (aspis_coredigestDigest32Inst.digest self.hash) s3
  ProverRwOrderedOracle.pure { self with state := a1 }

def materializeK {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
    (self : host_transcript.Transcript H) (row : U8) (payload : Slice U8)
    {α : Type} (k : host_transcript.Transcript H → Blocks → Blocks → Execution α) :
    Execution α := do
  let self1 ← absorb aspis_coredigestDigest32Inst self row
      payload
  let a := Array.repeat 32#usize 0#u8
  let blocks := Array.repeat 8#usize a
  let s ← native (Aeneas.Std.lift (Array.to_slice self1.state))
  let s1 ← native (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 1#u8 ])))
  let s2 ← native (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s, s1 ])))
  let a1 ← query (aspis_coredigestDigest32Inst.digest self1.hash) s2
  let pair ← native (Array.index_mut_usize blocks 0#usize)
  let index_mut_back := pair.2
  let s3 ← native (Aeneas.Std.lift (Array.to_slice self1.state))
  let s4 ← native (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 2#u8 ])))
  let s5 ← native (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s3, s4 ])))
  let a2 ← query (aspis_coredigestDigest32Inst.digest self1.hash) s5
  let blocks1 := index_mut_back a2
  let state ← native (Array.index_usize blocks1 0#usize)
  let s6 ← native (Aeneas.Std.lift (Array.to_slice state))
  let s7 ← native (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 1#u8 ])))
  let s8 ← native (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s6, s7 ])))
  let a3 ← query (aspis_coredigestDigest32Inst.digest self1.hash) s8
  let blocks2 := index_mut_back a1
  let blocks3 ← native (Array.update blocks2 1#usize a3)
  let s9 ← native (Aeneas.Std.lift (Array.to_slice state))
  let s10 ← native (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 2#u8 ])))
  let s11 ← native (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s9, s10 ])))
  let a4 ← query (aspis_coredigestDigest32Inst.digest self1.hash) s11
  let blocks4 ← native (Array.update blocks1 1#usize a4)
  let state1 ← native (Array.index_usize blocks4 1#usize)
  let s12 ← native (Aeneas.Std.lift (Array.to_slice state1))
  let s13 ← native (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 1#u8 ])))
  let s14 ← native (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s12, s13 ])))
  let a5 ← query (aspis_coredigestDigest32Inst.digest self1.hash) s14
  let blocks5 ← native (Array.update blocks3 2#usize a5)
  let s15 ← native (Aeneas.Std.lift (Array.to_slice state1))
  let s16 ← native (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 2#u8 ])))
  let s17 ← native (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s15, s16 ])))
  let a6 ← query (aspis_coredigestDigest32Inst.digest self1.hash) s17
  let blocks6 ← native (Array.update blocks4 2#usize a6)
  let state2 ← native (Array.index_usize blocks6 2#usize)
  let s18 ← native (Aeneas.Std.lift (Array.to_slice state2))
  let s19 ← native (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 1#u8 ])))
  let s20 ← native (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s18, s19 ])))
  let a7 ← query (aspis_coredigestDigest32Inst.digest self1.hash) s20
  let blocks7 ← native (Array.update blocks5 3#usize a7)
  let s21 ← native (Aeneas.Std.lift (Array.to_slice state2))
  let s22 ← native (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 2#u8 ])))
  let s23 ← native (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s21, s22 ])))
  let a8 ← query (aspis_coredigestDigest32Inst.digest self1.hash) s23
  let blocks8 ← native (Array.update blocks6 3#usize a8)
  let state3 ← native (Array.index_usize blocks8 3#usize)
  let s24 ← native (Aeneas.Std.lift (Array.to_slice state3))
  let s25 ← native (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 1#u8 ])))
  let s26 ← native (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s24, s25 ])))
  let a9 ← query (aspis_coredigestDigest32Inst.digest self1.hash) s26
  let blocks9 ← native (Array.update blocks7 4#usize a9)
  let s27 ← native (Aeneas.Std.lift (Array.to_slice state3))
  let s28 ← native (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 2#u8 ])))
  let s29 ← native (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s27, s28 ])))
  let a10 ← query (aspis_coredigestDigest32Inst.digest self1.hash) s29
  let blocks10 ← native (Array.update blocks8 4#usize a10)
  let state4 ← native (Array.index_usize blocks10 4#usize)
  let s30 ← native (Aeneas.Std.lift (Array.to_slice state4))
  let s31 ← native (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 1#u8 ])))
  let s32 ← native (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s30, s31 ])))
  let a11 ← query (aspis_coredigestDigest32Inst.digest self1.hash) s32
  let blocks11 ← native (Array.update blocks9 5#usize a11)
  let s33 ← native (Aeneas.Std.lift (Array.to_slice state4))
  let s34 ← native (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 2#u8 ])))
  let s35 ← native (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s33, s34 ])))
  let a12 ← query (aspis_coredigestDigest32Inst.digest self1.hash) s35
  let blocks12 ← native (Array.update blocks10 5#usize a12)
  let state5 ← native (Array.index_usize blocks12 5#usize)
  let s36 ← native (Aeneas.Std.lift (Array.to_slice state5))
  let s37 ← native (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 1#u8 ])))
  let s38 ← native (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s36, s37 ])))
  let a13 ← query (aspis_coredigestDigest32Inst.digest self1.hash) s38
  let blocks13 ← native (Array.update blocks11 6#usize a13)
  let s39 ← native (Aeneas.Std.lift (Array.to_slice state5))
  let s40 ← native (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 2#u8 ])))
  let s41 ← native (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s39, s40 ])))
  let a14 ← query (aspis_coredigestDigest32Inst.digest self1.hash) s41
  let blocks14 ← native (Array.update blocks12 6#usize a14)
  let state6 ← native (Array.index_usize blocks14 6#usize)
  let s42 ← native (Aeneas.Std.lift (Array.to_slice state6))
  let s43 ← native (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 1#u8 ])))
  let s44 ← native (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s42, s43 ])))
  let a15 ← query (aspis_coredigestDigest32Inst.digest self1.hash) s44
  let blocks15 ← native (Array.update blocks13 7#usize a15)
  let s45 ← native (Aeneas.Std.lift (Array.to_slice state6))
  let s46 ← native (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 2#u8 ])))
  let s47 ← native (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s45, s46 ])))
  let a16 ← query (aspis_coredigestDigest32Inst.digest self1.hash) s47
  let blocks16 ← native (Array.update blocks14 7#usize a16)
  let _ ← native (Array.index_usize blocks16 7#usize)
  k self1 blocks15 blocks16

def materialize {H : Type} (hash : aspis_core.digest.Digest32 H)
    (self : host_transcript.Transcript H) (row : U8) (payload : Slice U8) :=
  materializeK hash self row payload (fun s b a => ProverRwOrderedOracle.pure (s,b,a))
end R1Z.ProverRwOrderedQuerySource
