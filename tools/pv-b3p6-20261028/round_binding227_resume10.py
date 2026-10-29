"""Bind full-round fixed loops through four-lane named source equations."""
from pathlib import Path
import re,json,sys,hashlib
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';O=D/'resume10';files={};records=[]
header='''namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false
'''
# Keep the loop index list literal symbolic; no arithmetic or field evaluation.
for kind in ['q','m']:
 suffix='full_round'if kind=='q'else'full_round_m31_constants';raw=(L/'PV_B3P_P227_05.lean').read_text();a=raw.index('def reference_poseidon.'+suffix+'\n');b=raw.index('\n/--',a);decl=raw[a:b];body=decl.split(':= do\n',1)[1].rstrip();lines=body.splitlines();final=lines[-1];lines=lines[:-1]
 # The emitted array update ending each iteration is an exact stage boundary.
 ends=[i+1 for i,line in enumerate(lines)if re.match(r'  let state\d+ ← Array.update',line)];assert len(ends)==16
 cells=[lines[a:b]for a,b in zip([0]+ends[:-1],ends)]
 ctype='aspis_core.field.QM31'if kind=='q'else'U32'
 step=f'round_{kind}_step10';gp=f'round_{kind}_group10';tail=f'round_{kind}_source10';folded=f'round_{kind}_folded10';eq=f'round_{kind}_equation10'
 pp=f'(constants1 : Array {ctype} 16#usize)'
 base=f'PV_B3P_Round{kind.upper()}Step10227'
 stepbody='\n'.join(cells[0]);stepbody=re.sub(r'0#usize','index',stepbody);last=re.findall(r'  let (state\d+) ← Array.update',stepbody)[-1];stepbody+='\n  .ok '+last
 s='import PV_B3P_P227_05\nimport PV_B3P_Ordered227\nimport PV_B3P_DigestCpsEq9227\n'+header+('abbrev RoundState10 := Array aspis_core.field.QM31 16#usize\n'if kind=='q'else'')+f'\ndef {step} {pp} (state : RoundState10) (index : Usize) : Result RoundState10 := do\n'+stepbody+'\n'
 for n in [0,4,8,12]:s+=f'\ndef {gp}_{n:02} {pp} (state : RoundState10) : Result RoundState10 :=\n  PV_B3P_Ordered227.fold ({step} constants1) ['+', '.join(f'{i}#usize'for i in range(n,n+4))+'] state\n'
 s+='end PV_B3P_Binding10227\n'
 if kind=='m':s='import PV_B3P_RoundQStep10227\n'+s
 files[base]=s
 for n in reversed([4,8,12]):
  idx=n//4;incoming='state'+str(n if kind=='q'else 2*n);tailbody='\n'.join(sum(cells[n:],[]));tailbody=re.sub(r'\b'+incoming+r'\b','state',tailbody);out='state16'if kind=='q'else'state32';tailbody+='\n  finish '+out
  m=f'PV_B3P_Round{kind.upper()}Tail10{n:02}227';nextn=n+4
  imports=f'import {base}\n'+(f'import PV_B3P_Round{kind.upper()}Tail10{nextn:02}227\n'if n<12 else'')
  s=imports+header+f'\ndef {tail}_{n:02} {{β : Type}} (finish : RoundState10 → Result β) {pp} (state : RoundState10) : Result β := do\n'+tailbody+'\n'
  opaque='aspis_core.field.QM31.add aspis_core.field.M31.add reference_poseidon.pow5 Array.index_usize Array.update Array.index_mut_usize'
  s+='\nattribute [local irreducible] '+opaque+(f' {tail}_{nextn:02}'if n<12 else'')+'\n'
  right=(f'{tail}_{nextn:02} finish constants1'if n<12 else'finish')
  s+=f'''\ntheorem {eq}_{n:02} {{β : Type}} (finish : RoundState10 → Result β) {pp} (state : RoundState10) :
    {tail}_{n:02} finish constants1 state = ({gp}_{n:02} constants1 state >>= {right}) := by
  unfold {tail}_{n:02}
  conv_rhs => simp only [{gp}_{n:02},PV_B3P_Ordered227.fold,{step},PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
'''
  for j in range(sum(sum(' ←'in line for line in cell)for cell in cells[n:n+4])):
   # Pair binders from index_mut must be destructured before later heads.
   clines=[line for cell in cells[n:n+4]for line in cell if ' ←'in line]
   pair=clines[j].lstrip().startswith('let (')
   s+='  apply bind_equal9\n'+f'  intro head_{j}\n'
   if pair:s+=f'  rcases head_{j} with ⟨part_{j},back_{j}⟩\n'
  if n<12:s+=f'  unfold {tail}_{nextn:02}\n'
  s+='  rfl\n'
  # Composition uses only named equations and opaque four-lane groups.
  s+=f'\ndef {folded}_{n:02} {{β : Type}} (finish : RoundState10 → Result β) {pp} (state : RoundState10) : Result β :=\n  {gp}_{n:02} constants1 state >>= '+(f'{folded}_{nextn:02} finish constants1'if n<12 else'finish')+'\n'
  s+=f'\nattribute [local irreducible] {gp}_{n:02}\n'
  s+=f'\ntheorem round_{kind}_factor10_{n:02} {{β : Type}} (finish : RoundState10 → Result β) {pp} (state : RoundState10) :\n    {tail}_{n:02} finish constants1 state = {folded}_{n:02} finish constants1 state := by\n  rw [{eq}_{n:02}]\n'
  if n<12:
   s+=f'  change ({gp}_{n:02} constants1 state >>= {tail}_{nextn:02} finish constants1) = _\n  apply congrArg (fun next => {gp}_{n:02} constants1 state >>= next)\n  funext next\n  exact round_{kind}_factor10_{nextn:02} finish constants1 next\n'
  else:s+='  rfl\n'
  s+=f'\n#print axioms {eq}_{n:02}\n#print axioms round_{kind}_factor10_{n:02}\nend PV_B3P_Binding10227\n';files[m]=s
 # Two actual emitted callers share the exact prefix and differ only at the final call.
 for packed in [False,True]:
  name=suffix+('_packed'if packed else'');finish='reference_poseidon.external_linear_packed'if packed else'reference_poseidon.external_linear_lazy';rtype='Array aspis_core.field.QM31 '+('4'if packed else'16')+'#usize'
  m=f'PV_B3P_Round{kind.upper()}'+('Packed'if packed else'Plain')+'10227'
  s=f'import PV_B3P_Round{kind.upper()}Tail1004227\n'+header+'\nattribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.M31.add reference_poseidon.pow5 Array.index_usize Array.update Array.index_mut_usize '+tail+'_04\n'
  s+=f'''\ntheorem {name}_entry10 (state : RoundState10) {pp} :
    reference_poseidon.{name} state constants1 =
      ({gp}_00 constants1 state >>= {tail}_04 {finish} constants1) := by
  unfold reference_poseidon.{name}
  conv_rhs => simp only [{gp}_00,PV_B3P_Ordered227.fold,{step},PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
'''
  for j,line in enumerate([line for cell in cells[:4]for line in cell if ' ←'in line]):
   s+='  apply bind_equal9\n'+f'  intro head_{j}\n'
   if line.lstrip().startswith('let ('):s+=f'  rcases head_{j} with ⟨part_{j},back_{j}⟩\n'
  s+=f'  unfold {tail}_04\n  rfl\n'
  s+=f'''\ntheorem {name}_body_binding10 (state : RoundState10) {pp} :
    reference_poseidon.{name} state constants1 =
      ({gp}_00 constants1 state >>= {folded}_04 {finish} constants1) := by
  rw [{name}_entry10]
  apply congrArg (fun next => {gp}_00 constants1 state >>= next)
  funext next
  exact round_{kind}_factor10_04 {finish} constants1 next
#print axioms {name}_entry10
#print axioms {name}_body_binding10
end PV_B3P_Binding10227
''';files[m]=s;records.append(dict(body=name,module=m,theorem=f'{name}_body_binding10',source='crates/aspis-statement/src/state_only_poseidon.rs',source_loop='for lane in 0..POSEIDON2_WIDTH',iterations=16))
for m,s in files.items():
 p=L/(m+'.lean')
 if '--check'in sys.argv:assert p.read_text()==s,m
 else:p.write_text(s)
record=dict(modules=list(files),bodies=records,credit='emitted full-round bodies to ordered four-lane fold groups; source token-expansion check and std dependency bindings remain separate',semantic_use='reclassification within existing Charon/Aeneas tool trust')
p=O/'round-body-bindings.json'
if '--check'in sys.argv:assert json.loads(p.read_text())==record
else:p.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
