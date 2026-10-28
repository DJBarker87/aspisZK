"""Emit symbolic per-body success proofs by named monadic/field/array rules.
Only straight-line bodies are accepted; loops require separate invariant laws.
The generated proofs never compute a full body or use decide/native_decide.
"""
from pathlib import Path
import re,json,hashlib,sys
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';mapping={
 'aspis_core.field.QM31.add':'qadd','aspis_core.field.QM31.sub':'qsub','aspis_core.field.QM31.mul':'qmul','aspis_core.field.QM31.mul_m31':'qmul_m31','aspis_core.field.QM31.square':'qsquare',
 'aspis_core.field.CM31.add':'cadd','aspis_core.field.CM31.sub':'csub','aspis_core.field.CM31.mul':'cmul','aspis_core.field.CM31.mul_m31':'cmul_m31','aspis_core.field.CM31.square':'csquare','aspis_core.field.CM31.new':'cnew',
 'aspis_core.field.M31.add':'add','aspis_core.field.M31.sub':'sub','aspis_core.field.M31.mul':'mul','aspis_core.field.M31.reduce_u64':'reduce64','aspis_core.field.M31.reduce_u62':'reduce62','aspis_core.field.M31.double':'double',
 'Array.index_usize':'index','Array.update':'update','Array.index_mut_usize':'borrow','lift':'ok','ok':'ok'}
mapping['host_terminal_field.qm31_pack_base4_loop']='host_pack_loop_total'
mapping['reference_field.qm31_pack_base4_loop']='ref_pack_loop_total'
mapping.update({'reference_terminal.read227':'read_total',
 'reference_terminal.sum_interval227':'interval_total',
 'reference_terminal.initial_variant_selectors':'initial_variant_total',
 'reference_terminal.initial_lane227':'initial_lane_total',
 'reference_terminal.absorption_lane227':'absorption_lane_total'})
records=[]
def extract(mod):
 text=(L/(mod+'.lean')).read_text();blocks=re.split(r'(?=^def )',text,flags=re.M)[1:];out=[]
 for block in blocks:
  block=block.split('\n\n/--')[0].split('\nend PV_B3P_227')[0].split('\n\n#print')[0]
  m=re.match(r'def (\S+)(.*?)\s*:= do\s*\n?(.*)',block,re.S)
  if m:out.append((m[1],m[2],m[3]))
 return out

def emit(mod,source_mod,names,imports):
 out=['import PV_B3P_Success227',*['import '+x for x in imports],'namespace PV_B3P_Success227','open Aeneas Aeneas.Std PV_B3P_227','set_option autoImplicit false','']
 for name,head,body in extract(source_mod):
  if name not in names:continue
  # Balanced leading binders; the remainder is the result type.
  pos=0;binders=[];args=[]
  while True:
   while pos<len(head) and head[pos].isspace():pos+=1
   if pos==len(head) or head[pos] not in '({':break
   start=pos;stack=[]
   while pos<len(head):
    c=head[pos]
    if c in '({[':stack.append(c)
    if c in ')}]':
     stack.pop()
     if not stack:pos+=1;break
    pos+=1
   binder=head[start:pos];binders.append(binder)
   ns=binder[1:-1].split(':',1)[0].split();args += ['('+n+':='+n+')' if binder[0]=='{' else n for n in ns]
  theorem='total_'+name.replace('.','_')
  mapping[name]=theorem
  ispack=name in ['host_terminal_field.qm31_pack_base4','reference_field.qm31_pack_base4']
  if ispack:
   binders.append('(hlen : (Slice.len values).val ≤ 4)')
   body=body.replace('  massert (i <= 4#usize)\n','')
  assert not re.search(r'\b(if|match|loop|massert)\b',body),(name,'non-straightline')
  body='  '+body.lstrip()
  lets=list(re.finditer(r'^  let (.*?)\s*(←|:=)\s*',body,re.M))
  proof=[] if name=='reference_poseidon.global_sums227' else ['  unfold '+name]
  if name=='reference_terminal.semantic_initial_and_absorption':
   proof += ['  have rate8 : aspis_statement.poseidon2.RATE.val=8 := by unfold aspis_statement.poseidon2.RATE; rfl',
    '  have rate9 : (Usize.wrapping_add aspis_statement.poseidon2.RATE 1#usize).val=9 := by',
    '    have h := PV_B3P_Offset226V3.add_value aspis_statement.poseidon2.RATE 1#usize (by have hsize := usize_1024_size; change aspis_statement.poseidon2.RATE.val+1 < _; omega)',
    '    simpa only [rate8,show (1#usize).val=1 from rfl] using h']
  if ispack:proof += ['  have hb : Slice.len values ≤ 4#usize := by scalar_tac','  simp only [massert,hb,↓reduceIte,bind_tc_ok]']
  def rule(expr):
   call=expr.split()[0];assert call in mapping,(name,call,expr)
   target=mapping[call]
   if target in ['index','update','borrow']:return 'apply '+target+' <;> scalar_tac'
   if target in ['host_pack_loop_total','ref_pack_loop_total','read_total','interval_total']:return 'apply '+target+' <;> scalar_tac'
   if target=='ok':return 'exact ok _'
   return 'apply '+target
  for j,m in enumerate(lets):
   end=lets[j+1].start()if j+1<len(lets)else None
   expr=body[m.end():end].strip()
   if j+1==len(lets):
    # The last let expression ends before its final tail-call at indentation2.
    tail=re.search(r'\n  (?!let |\s)(.*)',expr,re.S)
    assert tail,(name,'tail missing')
    tail_expr=tail[1].strip();expr=expr[:tail.start()].strip()
   if m[2]==':=':
    # Preserve the already checked restoration-let proof text.
    if name=='reference_field.accumulate_prepared227':proof.append('  dsimp only')
    continue
   if name=='reference_terminal.semantic_initial_and_absorption' and expr.split()[0]=='lift':
    proof+=['  rw [PV_B3P_PureBind227.lift_bind]']
    continue
   proof+=['  apply bind','  · '+rule(expr)]
   pat=m[1].strip()
   if pat.startswith('('):proof+=['  intro pair','  rcases pair with ⟨'+pat[1:-1]+'⟩']
   else:proof+=['  intro '+pat]
  if not lets:tail_expr=body.strip()
  proof+=['  '+rule(tail_expr)]
  out += ['theorem '+theorem+' '+ ' '.join(binders)+' :\n    Success ('+name+' '+' '.join(args)+') := by',*proof,'','#print axioms '+theorem,'']
  records.append(dict(theorem=theorem,source_body=name,source_module=source_mod,source_sha256=hashlib.sha256((L/(source_mod+'.lean')).read_bytes()).hexdigest(),binds=sum(m[2]=='←'for m in lets),method='named symbolic success rules; no concrete body evaluation'))
 out+=['end PV_B3P_Success227',''];p=L/(mod+'.lean');data='\n'.join(out)
 if '--check'in sys.argv:assert p.read_text()==data,p
 else:p.write_text(data)

emit('PV_B3P_HostSuccess227','PV_B3P_E227_09',[
 'host_terminal_field.cm31_mul_r','host_terminal_field.prepare_component','host_terminal_field.prepared_component_mul','host_terminal_field.PreparedQm31Multiplier.new','host_terminal_field.PreparedQm31Multiplier.mul','host_terminal_field.terminal_limb'],['PV_B3P_E227_09'])
emit('PV_B3P_RefFieldSuccess227','PV_B3P_E227_18',[
 'reference_field.cm31_mul_r','reference_field.prepare_component','reference_field.prepared_component_mul','reference_field.PreparedQm31Multiplier.new','reference_field.PreparedQm31Multiplier.mul','reference_field.reconstruct_component','reference_field.terminal_limb'],['PV_B3P_E227_18'])
emit('PV_B3P_EqualitySuccess227','PV_B3P_P227_12',[
 'reference_terminal.equality_factor','reference_terminal.equality_value'],['PV_B3P_P227_12'])
emit('PV_B3P_AccumulateSuccess227','PV_B3P_P227_00',['reference_field.accumulate_prepared227'],['PV_B3P_P227_00'])
emit('PV_B3P_DotSuccess227','PV_B3P_P227_01',['reference_field.qm31_sum_products3_prepared','reference_field.qm31_m31_dot'],['PV_B3P_P227_01','PV_B3P_RefFieldSuccess227','PV_B3P_AccumulateSuccess227'])
emit('PV_B3P_PoseidonBaseSuccess227','PV_B3P_P227_02',[
 'reference_poseidon.pow5','reference_poseidon.extension_limbs','reference_poseidon.extension_from_raw_limbs','reference_poseidon.add_global227'],['PV_B3P_P227_02'])
emit('PV_B3P_GlobalSumsSuccess227','PV_B3P_P227_02',['reference_poseidon.global_sums227'],['PV_B3P_PoseidonBaseSuccess227'])
emit('PV_B3P_HostPackSuccess227','PV_B3P_E227_10',['host_terminal_field.qm31_pack_base4'],['PV_B3P_PackLoopSuccess227'])
emit('PV_B3P_RefPackSuccess227','PV_B3P_E227_19',['reference_field.qm31_pack_base4'],['PV_B3P_PackLoopSuccess227'])
emit('PV_B3P_AbsorptionSuccess227','PV_B3P_P227_09',['reference_terminal.absorption_lanes_literal','reference_terminal.semantic_initial_and_absorption'],['PV_B3P_SemanticBasicsSuccess227','PV_B3P_PureBind227'])
if '--check'not in sys.argv:(D/'resume6/success-generator.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps(dict(theorems=len(records),check='--check'in sys.argv)))
