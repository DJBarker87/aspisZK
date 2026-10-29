"""Generate straight-line Poseidon success proofs using named symbolic rules.
No unfolding of an entire function; pure scalar values are preserved by lift_total.
"""
from pathlib import Path
import re,sys,json,hashlib
L=Path('evidence/pv-b3p6-20261028/lean');sys.path.insert(0,str(Path(__file__).parent))
# Import helper definitions without invoking the resume6 generator's emissions.
ns={};s=Path('tools/pv-b3p6-20261028/success227_resume6.py').read_text();exec(s.split("emit('PV_B3P_HostSuccess227'",1)[0],ns)
extract=ns['extract'];mapping=ns['mapping'];mapping['reference_poseidon.raw_limb227']='raw_limb_total'
for m in ['PV_B3P_PoseidonBaseSuccess227','PV_B3P_GlobalSumsSuccess227','PV_B3P_DotSuccess227','PV_B3P_RefFieldSuccess227','PV_B3P_HostSuccess227','PV_B3P_RefPackSuccess227']:
 for th,body in re.findall(r'^theorem (total_\S+)(.*?)(?=^theorem |\Z)', (L/(m+'.lean')).read_text(),re.M|re.S):
  call=re.search(r'Success \((\S+)',body)
  assert call,(m,th)
  mapping[call[1]]=th
mapping['reference_poseidon.EXTERNAL_LOCAL_LIMB_MODULUS_BOUND']='modulus_total'
records=[]
def emit(mod,srcs,imports):
 out=['import '+m for m in imports]+['namespace PV_B3P_Success227','open Aeneas Aeneas.Std PV_B3P_227','set_option autoImplicit false','']
 if mod=='PV_B3P_InternalSuccess227':
  out += ['/-- A grid offset stays below16 even if wrapping occurs: modulo never\nincreases a natural number. This lemma does not evaluate a field expression. -/\ntheorem grid_mul_bound (g : Usize) (hg : g.val<4) :\n    (Usize.wrapping_mul 4#usize g).val<16 := by\n  rw [Usize.wrapping_mul_val_eq]\n  change (4*g.val) % UScalar.size .Usize < 16\n  have hm := Nat.mod_le (4*g.val) (UScalar.size .Usize)\n  omega\n\ntheorem grid_add_bound (g offset : Usize) (hg : g.val<4) (ho : offset.val<4) :\n    (Usize.wrapping_add (Usize.wrapping_mul 4#usize g) offset).val<16 := by\n  rw [Usize.wrapping_add_val_eq,Usize.wrapping_mul_val_eq]\n  change ((4*g.val) % UScalar.size .Usize + offset.val) % UScalar.size .Usize < 16\n  have hm := Nat.mod_le (4*g.val) (UScalar.size .Usize)\n  have ha := Nat.mod_le ((4*g.val) % UScalar.size .Usize + offset.val) (UScalar.size .Usize)\n  omega\n\n#print axioms grid_mul_bound\n#print axioms grid_add_bound\n']
 if mod=='PV_B3P_PoseidonSuccess227':
  out += ['theorem round_even_bound (row : Usize) (hlo : 2≤row.val) (hhi : row.val≤8) :\n    (Usize.wrapping_mul 2#usize (Usize.wrapping_sub row 2#usize)).val<14 := by\n  rw [Usize.wrapping_mul_val_eq,\n    PV_B3P_Offset226V3.sub_value row 2#usize (by scalar_tac)]\n  change (2*(row.val-2)) % UScalar.size .Usize < 14\n  have hm := Nat.mod_le (2*(row.val-2)) (UScalar.size .Usize)\n  omega\n\ntheorem round_odd_bound (row : Usize) (hlo : 2≤row.val) (hhi : row.val≤8) :\n    (Usize.wrapping_add (Usize.wrapping_mul 2#usize (Usize.wrapping_sub row 2#usize)) 1#usize).val<14 := by\n  rw [Usize.wrapping_add_val_eq,Usize.wrapping_mul_val_eq,\n    PV_B3P_Offset226V3.sub_value row 2#usize (by scalar_tac)]\n  change ((2*(row.val-2)) % UScalar.size .Usize+1) % UScalar.size .Usize < 14\n  have hm := Nat.mod_le (2*(row.val-2)) (UScalar.size .Usize)\n  have ha := Nat.mod_le ((2*(row.val-2)) % UScalar.size .Usize+1) (UScalar.size .Usize)\n  omega\n\n#print axioms round_even_bound\n#print axioms round_odd_bound\n']
 for source in srcs:
  for name,head,body in extract(source):
   if name.endswith('.SHIFTS'):continue
   if re.search(r'\b(if|match|loop|massert)\b',body):continue
   pos=0;binders=[];args=[]
   while True:
    while pos<len(head) and head[pos].isspace():pos+=1
    if pos==len(head)or head[pos]not in '({':break
    start=pos;stack=[]
    while pos<len(head):
     c=head[pos]
     if c in '({[':stack.append(c)
     if c in ')}]':
      stack.pop()
      if not stack:pos+=1;break
     pos+=1
    b=head[start:pos];binders.append(b);args+=b[1:-1].split(':',1)[0].split()
   theorem='total_'+name.replace('.','_');mapping[name]=theorem
   if name=='reference_poseidon.interpolate_column227':pass
   lets=list(re.finditer(r'^  let (.*?)\s*(←|:=)\s*','  '+body.lstrip(),re.M));body='  '+body.lstrip();proof=[]
   def rule(expr):
    call=expr.split()[0];assert call in mapping,(name,call,expr)
    target=mapping[call]
    if name=='reference_poseidon.interpolated_internal_pair' and target=='index':return 'apply index; first | scalar_tac | (apply round_even_bound <;> scalar_tac) | (apply round_odd_bound <;> scalar_tac)'
    if name in ['reference_poseidon.external_linear_packed','reference_poseidon.evaluate_state_only_poseidon_oracle_projected'] and target=='index':return 'apply index; first | scalar_tac | (apply grid_mul_bound; scalar_tac) | (apply grid_add_bound <;> scalar_tac)'
    if target in ['index','update','borrow','raw_limb_total','total_reference_field_qm31_pack_base4']:return 'apply '+target+' <;> scalar_tac'
    if target=='ok':return 'exact ok _'
    return 'apply '+target
   for j,m in enumerate(lets):
    end=lets[j+1].start()if j+1<len(lets)else None;expr=body[m.end():end].strip()
    if j+1==len(lets):
     tail=re.search(r'\n  (?!let |\s)(.*)',expr,re.S);assert tail,(name,'tail missing');tail_expr=tail[1].strip();expr=expr[:tail.start()].strip()
    if m[2]==':=':continue
    if expr.startswith('lift '):proof+=['  apply lift_total'];continue
    proof+=['  apply bind','  · '+rule(expr)]
    pat=m[1].strip()
    if pat.startswith('('):proof+=['  rintro ⟨'+pat[1:-1]+'⟩']
    else:proof+=['  intro '+pat]
   if not lets:tail_expr=body.strip()
   proof+=['  '+rule(tail_expr)]
   out+=['theorem '+theorem+' '+' '.join(binders)+' :\n    Success ('+name+' '+' '.join(args)+') := by',*proof,'','#print axioms '+theorem,'']
   records.append(dict(theorem=theorem,body=name,module=source,source_sha256=hashlib.sha256((L/(source+'.lean')).read_bytes()).hexdigest(),binds=sum(m[2]=='←'for m in lets),classification='reclassification within existing Charon/Aeneas tool trust'))
 out+=['end PV_B3P_Success227',''];p=L/(mod+'.lean');data='\n'.join(out)
 if '--check'in sys.argv:assert p.read_text()==data
 else:p.write_text(data)
emit('PV_B3P_ExternalSuccess227',['PV_B3P_P227_03a','PV_B3P_P227_03b','PV_B3P_P227_03d'],['PV_B3P_PoseidonCellsSuccess227','PV_B3P_GlobalSumsSuccess227','PV_B3P_P227_03'])
emit('PV_B3P_InternalSuccess227',['PV_B3P_P227_04'],['PV_B3P_ExternalSuccess227','PV_B3P_P227_04'])
emit('PV_B3P_RoundSuccess227',['PV_B3P_P227_05'],['PV_B3P_InternalSuccess227','PV_B3P_P227_05'])
emit('PV_B3P_PoseidonSuccess227',['PV_B3P_P227_06'],['PV_B3P_RoundSuccess227','PV_B3P_DotSuccess227','PV_B3P_RefPackSuccess227','PV_B3P_P227_06'])
if '--check'not in sys.argv:Path('evidence/pv-b3p6-20261028/resume7/poseidon-generator.json').write_text(json.dumps(records,indent=2)+'\n')
print(len(records))
