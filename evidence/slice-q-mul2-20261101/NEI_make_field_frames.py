from pathlib import Path
import json
E=Path(__file__).resolve().parent;ops=json.loads((E/'NEI_FIELD_FIXTURES.json').read_text())['ops']
proof={'m_add':('NEI_FieldScalar.m_add','M31.add'),'m_sub':('NEI_FieldScalar.m_sub','M31.sub'),'m_double':('NEI_FieldScalar.m_double','M31.double'),'reduce':('NEI_FieldScalar.reduce','reduce_u64'),'m_reduce':('NEI_FieldScalar.m_reduce_u64','M31.reduce_u64'),'m_mul':('NEI_FieldScalar.m_mul','M31.mul'),'cm_add':('NEI_FieldCM.cm_add','CM31.add'),'cm_sub':('NEI_FieldCM.cm_sub','CM31.sub'),'cm_mul':('NEI_FieldCM.cm_mul','CM31.mul'),'cm_mul_m31':('NEI_FieldCM.cm_mul_m31','CM31.mul_m31'),'by_r':('NEI_FieldCM.by_r','mul_by_r'),'qm_add':('NEI_FieldQM.qm_add','QM31.add'),'qm_sub':('NEI_FieldQM.qm_sub','QM31.sub'),'qm_mul':('NEI_FieldQM.qm_mul','QM31.mul'),'qm_mul_m31':('NEI_FieldQM.qm_mul_m31','QM31.mul_m31'),'mul_u':('NEI_FieldQM.mul_u','wide_exact.mul_u'),'wide_add':('NEI_FieldWide.wide_add','wide_exact.WideExact.add'),'wide_sub':('NEI_FieldWide.wide_sub','wide_exact.WideExact.sub'),'wide_mul':('NEI_FieldWide.wide_mul','wide_exact.WideExact.mul'),'wide_mul_m31':('NEI_FieldWide.wide_mul_m31','wide_exact.WideExact.mul_m31')}
s='''import NEI_FieldWide
set_option autoImplicit false
noncomputable section
namespace NEI_FieldFrames
open Aeneas Aeneas.Std Result NEI_FieldCarriers
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20
def run {A B S Event : Type} (map:A→B) (state:S) (result:Result A) : Result (B × S × List Event) := do
 let value ← result;ok (map value,state,[])
theorem mapped {A B S Event : Type} (map:A→B) (state:S) (actual:Result A) (model:Result B)
 (same:resultMap map actual=model) :
 run (Event:=Event) map state actual=run (Event:=Event) id state model := by
 rw [← same];cases actual <;> rfl
theorem widen (x:U32) : (core.convert.num.FromU64U32.from x).val=x.val := by
 change (UScalar.cast .U64 x).val=x.val
 rw [UScalar.cast_val_eq]
 apply Nat.mod_eq_of_lt
 have bound:=x.hSize
 norm_num [UScalar.size,UScalarTy.numBits,U32.size,U32.numBits,U64.size,U64.numBits] at bound ⊢
 omega
'''
for name,fn,kind,args in ops:
 typ={'word':'U32','cm':'N.C','qm':'N.Q','wide':'N.E'}[kind];argstr={'xy':f'(x y:{typ})','xs':f'(x:{typ}) (y:U32)','x':f'(x:{typ})','u':'(x:U64)'}[args]
 inputs='x y' if args in ['xy','xs'] else 'x';mapfn={'word':'id','cm':'toC','qm':'toQ','wide':'toE'}[kind]
 modelinputs=inputs if kind=='word' else ('('+mapfn+' x) '+('('+mapfn+' y)' if args=='xy' else 'y') if args in ['xy','xs'] else '('+mapfn+' x)')
 theorem,modelname=proof[name]
 s+=f'theorem {name} {{S Event:Type}} (state:S) {argstr} :\n run (Event:=Event) {mapfn} state (NEI_LineFull.aspis_core.field.{fn} {inputs}) =\n run (Event:=Event) id state (AspisR1CurrentWide.field.{modelname} {modelinputs}) := by\n'
 if kind=='word':s+=f' rw [{theorem}]\n'
 else:s+=f' exact mapped {mapfn} state _ _ ({theorem} {inputs})\n'
 s+=f'#print axioms {name}\n'
s+='#print axioms mapped\n#print axioms widen\nend NEI_FieldFrames\nend\n';(E/'NEI_FieldFrames.lean').write_text(s)
