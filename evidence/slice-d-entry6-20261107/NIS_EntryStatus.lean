import NHY_EntryHeader
import NHY_ParsedBodies
set_option autoImplicit false
namespace NIJ_EntryStatus
open Aeneas Aeneas.Std Result
abbrev Status := NCX_Reference.VerifierEntryStatusV1
abbrev Err := NCX_Reference.PoolV1VerifierRegistryFormatError

def value (v : U8) : core.result.Result Status Err :=
 match v with
 | 0#uscalar => .Ok .Pending
 | 1#uscalar => .Ok .Active
 | 2#uscalar => .Ok .Paused
 | 3#uscalar => .Ok .Retired
 | _ => .Err .InvalidStatus

theorem source (v : U8) : NCX_Reference.status v=ok (value v) := by
 unfold NCX_Reference.status value
 split <;> simp_all

/-- Invalid status is selected after the reserved suffix and before any field
or validator call. No parser success assumption is used. -/
theorem rejected (b : Slice U8) (len : Slice.len b=320#usize)
 (magic : NCX_Reference.magic b NCX_Reference.POOL_V1_VERIFIER_ENTRY_V2_MAGIC=ok true)
 (version : Slice.index_usize b 4#usize=ok 3#u8)
 (mode : Slice.index_usize b 7#usize=ok 1#u8)
 (zeros : NCX_Reference.zero (NHY_SliceRead.segment b 314 6)=ok true)
 (st : U8) (read : Slice.index_usize b 5#usize=ok st)
 (bad : value st=.Err .InvalidStatus) :
 NCX_Reference.decode_verifier_registry_entry_v2 b=ok (.Err .InvalidStatus) := by
 have length : b.val.length=320 := congrArg UScalar.val len
 have reserved:=NHY_SliceRead.read b 314#usize 320#usize (by scalar_tac) (by scalar_tac)
 have status : NCX_Reference.status st=ok (.Err .InvalidStatus) := by rw [source,bad]
 simp only [NCX_Reference.decode_verifier_registry_entry_v2,
  NCX_Reference.POOL_V1_VERIFIER_ENTRY_V2_BYTES,NCX_Reference.POOL_V1_VERIFIER_ENTRY_V2_VERSION,
  NCX_Reference.POOL_V1_VERIFIER_DEPLOYMENT_MODE_IMMUTABLE_LOADER_V3,
  len,magic,version,mode,reserved,zeros,read,status,
  show (320#usize != 320#usize)=false from rfl,
  show (3#u8 != 3#u8)=false from rfl,show (1#u8 != 1#u8)=false from rfl,
  show (314#usize).val=314 from rfl,show (320#usize).val=320 from rfl,Nat.reduceSub,
  Bool.false_eq_true,ite_false,ite_true,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
  core.convert.FromSame]
 rfl

#print axioms source
#print axioms rejected
end NIJ_EntryStatus
