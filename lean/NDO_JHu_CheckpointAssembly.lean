import NCV_Reference.Funs
import NDO_JHg_FieldRead
set_option autoImplicit false
namespace AspisR1.JHu_CheckpointAssembly
open Aeneas Aeneas.Std Result

/-- Symbolic composition of the complete E008 checkpoint decoder. -/
theorem source (b : Slice U8) (v : NCV_Reference.Checkpoint)
    (len : Slice.len b=192#usize)
    (prefixRead : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      b {«end»:=4#usize}=ok (JHg_FieldRead.segment b 0 4))
    (magic : NCV_Reference.equal (JHg_FieldRead.segment b 0 4)
      (Array.make 4#usize [65#u8,83#u8,67#u8,56#u8]).to_slice=ok true)
    (version : Slice.index_usize b 4#usize=ok 2#u8)
    (lanes : Slice.index_usize b 5#usize=ok 8#u8)
    (kind : Slice.index_usize b 6#usize=ok 1#u8)
    (suffix : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
      b {start:=176#usize}=ok (JHg_FieldRead.segment b 176 16))
    (reserved : NCV_Reference.zero (JHg_FieldRead.segment b 176 16)=ok true)
    (master : NCV_Reference.bytes32 b 8#usize=ok v.master)
    (domain : NCV_Reference.bytes32 b 40#usize=ok v.deployment_domain)
    (masterNonzero : NCV_Reference.zero v.master.to_slice=ok false)
    (domainNonzero : NCV_Reference.zero v.deployment_domain.to_slice=ok false)
    (root : NCV_Reference.digest b 80#usize=ok (.Ok v.global_root))
    (seq : NCV_Reference.sequences b 112#usize=ok v.lane_sequences)
    (seqValid : NCV_Reference.valid_sequences v.lane_sequences=ok true)
    (bump : Slice.index_usize b 7#usize=ok v.bump)
    (counter : NCV_Reference.word64 b 72#usize=ok v.checkpoint_sequence) :
    NCV_Reference.decode_checkpoint_ref b=ok (.Ok v) := by
  cases v
  simp only [NCV_Reference.decode_checkpoint_ref,len,
    show (192#usize != 192#usize)=false from rfl,Bool.false_eq_true,ite_false,
    prefixRead,lift,bind_tc_ok,magic,ite_true,version,lanes,kind,
    show (2#u8 != 2#u8)=false from rfl,
    show (8#u8 != 8#u8)=false from rfl,
    show (1#u8 != 1#u8)=false from rfl,
    suffix,reserved,master,domain,masterNonzero,domainNonzero,root,seq,seqValid,bump,counter,
    core.result.Result.Insts.CoreOpsTry.branch]
#print axioms source
end AspisR1.JHu_CheckpointAssembly
