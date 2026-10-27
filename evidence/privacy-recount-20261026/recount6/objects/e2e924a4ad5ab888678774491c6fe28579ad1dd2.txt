import R1Z.ProverRwQueryResult
set_option autoImplicit false
namespace R1Z.ProverRwQueryMaterial
open Aeneas Aeneas.Std Result ProverRwFull ProverRwQueryScan
variable [ExternalTypes] [ExternalFuns]

def materializeK {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
    (self : host_transcript.Transcript H) (row : U8) (payload : Slice U8)
    {α : Type} (k : host_transcript.Transcript H → Blocks → Blocks → Result α) :
    Result α := do
  let self1 ←
    host_transcript.Transcript.absorb aspis_coredigestDigest32Inst self row
      payload
  let a := Array.repeat 32#usize 0#u8
  let blocks := Array.repeat 8#usize a
  let s ← Aeneas.Std.lift (Array.to_slice self1.state)
  let s1 ← Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
  let s2 ← Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s, s1 ]))
  let a1 ← aspis_coredigestDigest32Inst.digest self1.hash s2
  let pair ← Array.index_mut_usize blocks 0#usize
  let index_mut_back := pair.2
  let s3 ← Aeneas.Std.lift (Array.to_slice self1.state)
  let s4 ← Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
  let s5 ← Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s3, s4 ]))
  let a2 ← aspis_coredigestDigest32Inst.digest self1.hash s5
  let blocks1 := index_mut_back a2
  let state ← Array.index_usize blocks1 0#usize
  let s6 ← Aeneas.Std.lift (Array.to_slice state)
  let s7 ← Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
  let s8 ← Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s6, s7 ]))
  let a3 ← aspis_coredigestDigest32Inst.digest self1.hash s8
  let blocks2 := index_mut_back a1
  let blocks3 ← Array.update blocks2 1#usize a3
  let s9 ← Aeneas.Std.lift (Array.to_slice state)
  let s10 ← Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
  let s11 ← Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s9, s10 ]))
  let a4 ← aspis_coredigestDigest32Inst.digest self1.hash s11
  let blocks4 ← Array.update blocks1 1#usize a4
  let state1 ← Array.index_usize blocks4 1#usize
  let s12 ← Aeneas.Std.lift (Array.to_slice state1)
  let s13 ← Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
  let s14 ← Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s12, s13 ]))
  let a5 ← aspis_coredigestDigest32Inst.digest self1.hash s14
  let blocks5 ← Array.update blocks3 2#usize a5
  let s15 ← Aeneas.Std.lift (Array.to_slice state1)
  let s16 ← Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
  let s17 ← Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s15, s16 ]))
  let a6 ← aspis_coredigestDigest32Inst.digest self1.hash s17
  let blocks6 ← Array.update blocks4 2#usize a6
  let state2 ← Array.index_usize blocks6 2#usize
  let s18 ← Aeneas.Std.lift (Array.to_slice state2)
  let s19 ← Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
  let s20 ← Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s18, s19 ]))
  let a7 ← aspis_coredigestDigest32Inst.digest self1.hash s20
  let blocks7 ← Array.update blocks5 3#usize a7
  let s21 ← Aeneas.Std.lift (Array.to_slice state2)
  let s22 ← Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
  let s23 ← Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s21, s22 ]))
  let a8 ← aspis_coredigestDigest32Inst.digest self1.hash s23
  let blocks8 ← Array.update blocks6 3#usize a8
  let state3 ← Array.index_usize blocks8 3#usize
  let s24 ← Aeneas.Std.lift (Array.to_slice state3)
  let s25 ← Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
  let s26 ← Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s24, s25 ]))
  let a9 ← aspis_coredigestDigest32Inst.digest self1.hash s26
  let blocks9 ← Array.update blocks7 4#usize a9
  let s27 ← Aeneas.Std.lift (Array.to_slice state3)
  let s28 ← Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
  let s29 ← Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s27, s28 ]))
  let a10 ← aspis_coredigestDigest32Inst.digest self1.hash s29
  let blocks10 ← Array.update blocks8 4#usize a10
  let state4 ← Array.index_usize blocks10 4#usize
  let s30 ← Aeneas.Std.lift (Array.to_slice state4)
  let s31 ← Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
  let s32 ← Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s30, s31 ]))
  let a11 ← aspis_coredigestDigest32Inst.digest self1.hash s32
  let blocks11 ← Array.update blocks9 5#usize a11
  let s33 ← Aeneas.Std.lift (Array.to_slice state4)
  let s34 ← Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
  let s35 ← Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s33, s34 ]))
  let a12 ← aspis_coredigestDigest32Inst.digest self1.hash s35
  let blocks12 ← Array.update blocks10 5#usize a12
  let state5 ← Array.index_usize blocks12 5#usize
  let s36 ← Aeneas.Std.lift (Array.to_slice state5)
  let s37 ← Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
  let s38 ← Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s36, s37 ]))
  let a13 ← aspis_coredigestDigest32Inst.digest self1.hash s38
  let blocks13 ← Array.update blocks11 6#usize a13
  let s39 ← Aeneas.Std.lift (Array.to_slice state5)
  let s40 ← Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
  let s41 ← Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s39, s40 ]))
  let a14 ← aspis_coredigestDigest32Inst.digest self1.hash s41
  let blocks14 ← Array.update blocks12 6#usize a14
  let state6 ← Array.index_usize blocks14 6#usize
  let s42 ← Aeneas.Std.lift (Array.to_slice state6)
  let s43 ← Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
  let s44 ← Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s42, s43 ]))
  let a15 ← aspis_coredigestDigest32Inst.digest self1.hash s44
  let blocks15 ← Array.update blocks13 7#usize a15
  let s45 ← Aeneas.Std.lift (Array.to_slice state6)
  let s46 ← Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
  let s47 ← Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s45, s46 ]))
  let a16 ← aspis_coredigestDigest32Inst.digest self1.hash s47
  let blocks16 ← Array.update blocks14 7#usize a16
  let _ ← Array.index_usize blocks16 7#usize
  k self1 blocks15 blocks16


def materialize {H : Type} (hash : aspis_core.digest.Digest32 H)
    (self : host_transcript.Transcript H) (row : U8) (payload : Slice U8) :=
  materializeK hash self row payload (fun s b a => ok (s,b,a))

theorem materialize_bind {H α : Type} (hash : aspis_core.digest.Digest32 H)
    (self : host_transcript.Transcript H) (row : U8) (payload : Slice U8)
    (k : host_transcript.Transcript H → Blocks → Blocks → Result α) :
    (materialize hash self row payload >>= fun p => k p.1 p.2.1 p.2.2) =
    materializeK hash self row payload k := by
  simp only [materialize, materializeK, bind_assoc_eq, bind_tc_ok]

#print axioms materialize_bind
end R1Z.ProverRwQueryMaterial
