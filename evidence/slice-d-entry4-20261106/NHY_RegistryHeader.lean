import NCX_Reference.Funs
import NHY_SliceRead
set_option autoImplicit false
namespace NHY_RegistryHeader
open Aeneas Aeneas.Std Result
open NCX_Reference

theorem wrong_length (b : Slice U8) (h : Slice.len b ≠ 256#usize) :
    decode_verifier_registry_v2 b=ok (.Err .WrongLength) := by
  have bad : (Slice.len b != 256#usize)=true := bne_iff_ne.mpr h
  simp only [decode_verifier_registry_v2,POOL_V1_VERIFIER_REGISTRY_V2_BYTES,bad,ite_true]

theorem wrong_magic (b : Slice U8) (len : Slice.len b=256#usize)
    (magic : NCX_Reference.magic b POOL_V1_VERIFIER_REGISTRY_V2_MAGIC=ok false) :
    decode_verifier_registry_v2 b=ok (.Err .WrongMagic) := by
  simp only [decode_verifier_registry_v2,POOL_V1_VERIFIER_REGISTRY_V2_BYTES,len,magic,
    show (256#usize != 256#usize)=false from rfl,
    Bool.false_eq_true,ite_false,bind_tc_ok]

theorem wrong_version (b : Slice U8) (len : Slice.len b=256#usize)
    (magic : NCX_Reference.magic b POOL_V1_VERIFIER_REGISTRY_V2_MAGIC=ok true)
    (version : U8) (read : Slice.index_usize b 4#usize=ok version)
    (different : version ≠ 3#u8) :
    decode_verifier_registry_v2 b=ok (.Err .WrongVersion) := by
  have bad : (version != 3#u8)=true := bne_iff_ne.mpr different
  simp only [decode_verifier_registry_v2,POOL_V1_VERIFIER_REGISTRY_V2_BYTES,POOL_V1_VERIFIER_REGISTRY_V2_VERSION,len,magic,read,
    show (256#usize != 256#usize)=false from rfl,
    bad,Bool.false_eq_true,ite_false,ite_true,bind_tc_ok]

theorem wrong_mode (b : Slice U8) (len : Slice.len b=256#usize)
    (magic : NCX_Reference.magic b POOL_V1_VERIFIER_REGISTRY_V2_MAGIC=ok true)
    (read_version : Slice.index_usize b 4#usize=ok 3#u8)
    (mode : U8) (read_mode : Slice.index_usize b 6#usize=ok mode)
    (different : mode ≠ 1#u8) :
    decode_verifier_registry_v2 b=ok (.Err .InvalidDeploymentMode) := by
  have bad : (mode != 1#u8)=true := bne_iff_ne.mpr different
  simp only [decode_verifier_registry_v2,POOL_V1_VERIFIER_REGISTRY_V2_BYTES,POOL_V1_VERIFIER_REGISTRY_V2_VERSION,POOL_V1_VERIFIER_DEPLOYMENT_MODE_IMMUTABLE_LOADER_V3,
    len,magic,read_version,read_mode,
    show (256#usize != 256#usize)=false from rfl,
    show (3#u8 != 3#u8)=false from rfl,
    bad,Bool.false_eq_true,ite_false,ite_true,bind_tc_ok]

theorem reserved (b : Slice U8) (len : Slice.len b=256#usize)
    (magic : NCX_Reference.magic b POOL_V1_VERIFIER_REGISTRY_V2_MAGIC=ok true)
    (read_version : Slice.index_usize b 4#usize=ok 3#u8)
    (read_mode : Slice.index_usize b 6#usize=ok 1#u8)
    (nonzero : NCX_Reference.zero (NHY_SliceRead.segment b 249 7)=ok false) :
    decode_verifier_registry_v2 b=ok (.Err .NonZeroReserved) := by
  have length : b.val.length=256 := congrArg UScalar.val len
  have window:=NHY_SliceRead.read b 249#usize 256#usize (by scalar_tac) (by scalar_tac)
  simp only [decode_verifier_registry_v2,POOL_V1_VERIFIER_REGISTRY_V2_BYTES,POOL_V1_VERIFIER_REGISTRY_V2_VERSION,POOL_V1_VERIFIER_DEPLOYMENT_MODE_IMMUTABLE_LOADER_V3,
    len,magic,read_version,read_mode,window,nonzero,
    show (249#usize).val=249 from rfl,show (256#usize).val=256 from rfl,Nat.reduceSub,
    show (256#usize != 256#usize)=false from rfl,
    show (3#u8 != 3#u8)=false from rfl,show (1#u8 != 1#u8)=false from rfl,
    Bool.false_eq_true,ite_false,ite_true,bind_tc_ok]

#print axioms wrong_length
#print axioms wrong_magic
#print axioms wrong_version
#print axioms wrong_mode
#print axioms reserved
end NHY_RegistryHeader
