from pathlib import Path
import re
L=Path('lean')
for family,key,total,res in [('Registry','registry',256,249),('Entry','entry',320,314)]:
 fun='decode_verifier_registry_v2' if key=='registry' else 'decode_verifier_registry_entry_v2'
 prefix='POOL_V1_VERIFIER_REGISTRY_V2_' if key=='registry' else 'POOL_V1_VERIFIER_ENTRY_V2_'
 audit=(L/f'JHg_Audit{family}.lean').read_text()
 names=re.findall(r'theorem (\w+) :',audit)
 s=f'''import NCX_{family}Value
set_option autoImplicit false
namespace NCX_{family}Fixture
open Aeneas Aeneas.Std Result AspisR1
open NCX_{family}Fields
attribute [local irreducible] JHb_Data{family}.bytes

theorem source : NCX_Reference.{fun} JHb_Data{family}.value=
    ok (.Ok NCX_{family}Value.value) := by
  have len : JHb_Data{family}.value.val.length={total} := JHb_Data{family}.length
  have size : Slice.len JHb_Data{family}.value={total}#usize := UScalar.eq_of_val_eq len
  have magic : NCX_Reference.magic JHb_Data{family}.value NCX_Reference.{prefix}MAGIC=ok true := by
    apply NCX_ZeroLaws.magic
    · omega
    · exact JHg_Audit{family}.magic
  have reserved:=JHg_FieldRead.read JHb_Data{family}.value {res}#usize {total}#usize (by scalar_tac) (by scalar_tac)
  have zeros : NCX_Reference.zero (JHg_FieldRead.segment JHb_Data{family}.value {res} {total-res})=ok true :=
    NCX_ZeroLaws.zero _ {total-res} JHg_Audit{family}.reserved (by omega)
  simp only [NCX_Reference.{fun},size,NCX_Reference.{prefix}BYTES,
    NCX_Reference.{prefix}VERSION,NCX_Reference.POOL_V1_VERIFIER_DEPLOYMENT_MODE_IMMUTABLE_LOADER_V3,
    magic,reserved,zeros,
'''
 s+='    '+','.join('read_'+n for n in names if n not in ['magic','reserved'])+',\n'
 s+=f'''    bind_tc_ok,show ({total}#usize != {total}#usize)=false from rfl,
    show (3#u8 != 3#u8)=false from rfl,show (1#u8 != 1#u8)=false from rfl,
    Bool.false_eq_true,ite_false,ite_true,
    show ({res}#usize).val={res} from rfl,show ({total}#usize).val={total} from rfl,Nat.reduceSub,
'''
 if key=='entry':s+='    NCX_Reference.status,core.result.Result.Insts.CoreOpsTry.branch,\n'
 s+=f'''    NCX_{family}Value.valid,core.result.Result.Insts.CoreOpsTry.branch]
  rfl
#print axioms source
end NCX_{family}Fixture
'''
 s=s.replace(f'    · exact JHg_Audit{family}.magic',f'    · simpa only [JHb_Data{family}.value,Array.make,List.drop_zero,NCX_Reference.{prefix}MAGIC] using JHg_Audit{family}.magic')
 s=s.replace('  simp only [NCX_Reference.decode_',f'  have valid:=NCX_{family}Value.valid\n  unfold NCX_{family}Value.value at valid\n  simp only [NCX_Reference.decode_').replace(f'NCX_{family}Value.valid,core.result','valid,core.result')
 if key=='entry':s=s.replace('import NCX_EntryValue','import NCX_EntryValue\nimport NCX_Status').replace('NCX_Reference.status,core.result','NCX_Status.active,core.result')
 (L/f'NCX_{family}Fixture.lean').write_text(s)
