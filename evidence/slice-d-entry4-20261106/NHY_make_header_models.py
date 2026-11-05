from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent
for tag,fn,size,kind,mode,start in [('Registry','decode_verifier_registry_v2',256,'REGISTRY',6,249),('Entry','decode_verifier_registry_entry_v2',320,'ENTRY',7,314)]:
 n='NHY_'+tag+'Header';prefix='POOL_V1_VERIFIER_'+kind+'_V2_';c=prefix+'BYTES';m=prefix+'MAGIC';v=prefix+'VERSION'
 s=f'''import NCX_Reference.Funs
import NHY_SliceRead
set_option autoImplicit false
namespace {n}
open Aeneas Aeneas.Std Result
open NCX_Reference

theorem wrong_length (b : Slice U8) (h : Slice.len b ≠ {size}#usize) :
    {fn} b=ok (.Err .WrongLength) := by
  simp only [{fn},{c},h,bne_iff_ne,ite_true]

theorem wrong_magic (b : Slice U8) (len : Slice.len b={size}#usize)
    (magic : NCX_Reference.magic b {m}=ok false) :
    {fn} b=ok (.Err .WrongMagic) := by
  simp only [{fn},{c},len,magic,
    show ({size}#usize != {size}#usize)=false from rfl,
    Bool.false_eq_true,ite_false,bind_tc_ok]

theorem wrong_version (b : Slice U8) (len : Slice.len b={size}#usize)
    (magic : NCX_Reference.magic b {m}=ok true)
    (version : U8) (read : Slice.index_usize b 4#usize=ok version)
    (different : version ≠ 3#u8) :
    {fn} b=ok (.Err .WrongVersion) := by
  simp only [{fn},{c},{v},len,magic,read,
    show ({size}#usize != {size}#usize)=false from rfl,
    different,bne_iff_ne,Bool.false_eq_true,ite_false,ite_true,bind_tc_ok]

theorem wrong_mode (b : Slice U8) (len : Slice.len b={size}#usize)
    (magic : NCX_Reference.magic b {m}=ok true)
    (read_version : Slice.index_usize b 4#usize=ok 3#u8)
    (mode : U8) (read_mode : Slice.index_usize b {mode}#usize=ok mode)
    (different : mode ≠ 1#u8) :
    {fn} b=ok (.Err .InvalidDeploymentMode) := by
  simp only [{fn},{c},{v},POOL_V1_VERIFIER_DEPLOYMENT_MODE_IMMUTABLE_LOADER_V3,
    len,magic,read_version,read_mode,
    show ({size}#usize != {size}#usize)=false from rfl,
    show (3#u8 != 3#u8)=false from rfl,
    different,bne_iff_ne,Bool.false_eq_true,ite_false,ite_true,bind_tc_ok]

theorem reserved (b : Slice U8) (len : Slice.len b={size}#usize)
    (magic : NCX_Reference.magic b {m}=ok true)
    (read_version : Slice.index_usize b 4#usize=ok 3#u8)
    (read_mode : Slice.index_usize b {mode}#usize=ok 1#u8)
    (nonzero : NCX_Reference.zero (NHY_SliceRead.segment b {start} {size-start})=ok false) :
    {fn} b=ok (.Err .NonZeroReserved) := by
  have length : b.val.length={size} := congrArg UScalar.val len
  have window:=NHY_SliceRead.read b {start}#usize {size}#usize (by scalar_tac) (by scalar_tac)
  simp only [{fn},{c},{v},POOL_V1_VERIFIER_DEPLOYMENT_MODE_IMMUTABLE_LOADER_V3,
    len,magic,read_version,read_mode,window,nonzero,
    show ({start}#usize).val={start} from rfl,show ({size}#usize).val={size} from rfl,Nat.reduceSub,
    show ({size}#usize != {size}#usize)=false from rfl,
    show (3#u8 != 3#u8)=false from rfl,show (1#u8 != 1#u8)=false from rfl,
    Bool.false_eq_true,ite_false,ite_true,bind_tc_ok]

'''
 for root in ['wrong_length','wrong_magic','wrong_version','wrong_mode','reserved']:s+='#print axioms '+root+'\n'
 s+='end '+n+'\n';(E/(n+'.lean')).write_text(s)
