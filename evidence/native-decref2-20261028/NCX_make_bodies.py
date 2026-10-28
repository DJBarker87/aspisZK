from pathlib import Path
L=Path('lean')
s='''import NCX_ZeroLaws
set_option autoImplicit false
namespace NCX_ParsedBodies
open Aeneas Aeneas.Std Result AspisR1

def validation {A : Type} (v : A) : core.result.Result Unit NCX_Reference.PoolV1VerifierRegistryFormatError →
    core.result.Result A NCX_Reference.PoolV1VerifierRegistryFormatError
  | .Ok () => .Ok v
  | .Err e => .Err e
'''
for key,size,res,ty,prefix,fun,validator,fields in [
('registry',256,249,'VerifierRegistryV2','REGISTRY','decode_verifier_registry_v2','validate_verifier_registry_v2',[(5,'flags','byte'),(7,'bump','byte'),(8,'pool','array'),(40,'authority','array'),(72,'policy_binding','array'),(104,'generation','word'),(112,'minimum_activation_delay_slots','word'),(120,'registry_program','array'),(152,'loader_program','array'),(184,'programdata_address','array'),(248,'programdata_bump','byte'),(216,'executable_hash','array')]),
('entry',320,314,'VerifierRegistryEntryV2','ENTRY','decode_verifier_registry_entry_v2','validate_verifier_registry_entry_v2',[(6,'statement_version','byte'),(312,'bump','byte'),(8,'pool','array'),(40,'verifier_program','array'),(72,'profile_binding','array'),(104,'release_binding','array'),(136,'loader_program','array'),(168,'programdata_address','array'),(313,'programdata_bump','byte'),(200,'executable_hash','array'),(232,'expected_upgrade_authority','array'),(264,'activation_slot','word'),(272,'retirement_slot','word'),(280,'policy_binding','array')])]:
 mode=6 if key=='registry' else 7
 const=f'POOL_V1_VERIFIER_{prefix}_V2_'
 s+=f'''\n/-- Parser assembly with every observed field explicit; no validation-success premise. -/
theorem {key} (b : Slice U8) (v : NCX_Reference.{ty})
    (size : Slice.len b={size}#usize)
    (magic : NCX_Reference.magic b NCX_Reference.{const}MAGIC=ok true)
    (version : Slice.index_usize b 4#usize=ok 3#u8)
    (mode : Slice.index_usize b {mode}#usize=ok 1#u8)
    (zeros : NCX_Reference.zero (JHg_FieldRead.segment b {res} {size-res})=ok true)
'''
 if key=='entry':
  s+='    (st : U8) (status_byte : Slice.index_usize b 5#usize=ok st)\n    (status : NCX_Reference.status st=ok (.Ok v.status))\n'
 for off,f,kind in fields:
  call='Slice.index_usize' if kind=='byte' else 'NCX_Reference.read32' if kind=='array' else 'NCX_Reference.word'
  s+=f'    (read_{f} : {call} b {off}#usize=ok v.{f})\n'
 s+=f'''    : NCX_Reference.{fun} b=
      (do let r ← NCX_Reference.{validator} v;ok (validation v r)) := by
  have length : b.val.length={size} := congrArg UScalar.val size
  have reserved:=JHg_FieldRead.read b {res}#usize {size}#usize (by scalar_tac) (by scalar_tac)
  simp only [NCX_Reference.{fun},size,NCX_Reference.{const}BYTES,
    NCX_Reference.{const}VERSION,NCX_Reference.POOL_V1_VERIFIER_DEPLOYMENT_MODE_IMMUTABLE_LOADER_V3,
    magic,version,mode,reserved,zeros,
    {','.join('read_'+f for _,f,_ in fields)},
    bind_tc_ok,show ({size}#usize != {size}#usize)=false from rfl,
    show (3#u8 != 3#u8)=false from rfl,show (1#u8 != 1#u8)=false from rfl,
    Bool.false_eq_true,ite_false,ite_true,show ({res}#usize).val={res} from rfl,
    show ({size}#usize).val={size} from rfl,Nat.reduceSub,
'''
 if key=='entry':s+='    status_byte,status,core.result.Result.Insts.CoreOpsTry.branch,\n'
 s+='    bind_tc_ok]\n'
 s+=f'''  cases h : NCX_Reference.{validator} v with
  | fail e => simp only [h,bind_tc_fail]
  | div => simp only [h,bind_tc_div]
  | ok r => cases r <;> rfl
#print axioms {key}
'''
s+='end NCX_ParsedBodies\n';(L/'NCX_ParsedBodies.lean').write_text(s)
