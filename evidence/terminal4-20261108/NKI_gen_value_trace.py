from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent;s=(E/'NKI_ValuePrefix.lean').read_text();body=s[s.index(' : Result Tail := do')+len(' : Result Tail := do'):s.index('  ok ⟨openings3')]
parts=re.split(r'^  let ',body,flags=re.M)[1:];binds=[];fields=[];pure=[]
for part in parts:
 if ' ←' not in part:
  name,expr=part.split(' :=',1);pure.append((name.strip(),expr.strip()));continue
 name,expr=part.split(' ←',1);name=name.strip();binds.append((name,expr.strip()))
 for n in [x.strip() for x in name.strip('()').split(',')]:
  ty='NQ'
  if n=='value_selectors':ty='Array NQ 3#usize'
  elif n.startswith('range') and n!='range_selector':ty='Array NQ 33#usize'
  elif n.startswith('openings'):ty='Openings'
  elif n in ['i','i1']:ty='U32'
  fields.append((n,ty))
head='''import NKI_ValueTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_ValueTrace
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open NKI_ValuePrefix (Openings Selectors Tail)
structure Locals where
'''+''.join(' '+n+' : '+ty+'\n' for n,ty in fields)
text=head+'def run (openings : Openings) (selectors : Selectors) : Result Locals := do\n'+body+'  ok ⟨'+','.join(n for n,_ in fields)+'⟩\n'
props=[]
for n,ty in fields:
 if ty=='NQ':props.append('Canon l.'+n)
 elif ty.startswith('Array'):props.append('canonical l.'+n)
 elif ty=='Openings':props.append('l.'+n+'=o')
text+='def Canonical (o : Openings) (l : Locals) : Prop :=\n '+' ∧\n '.join(props)+'\n'
text+='def output (l : Locals) : Tail := ⟨l.openings3,l.range_selector,l.range6⟩\n'
text+='def Clauses (openings : Openings) (selectors : Selectors) (l : Locals) : Prop :=\n'+''.join(' let '+n+':=l.'+n+'\n' for n,_ in fields)+''.join(' let '+n+':='+e+'\n' for n,e in pure)+' ∧\n'.join(' ('+expr+'=ok '+name+')' for name,expr in binds)+'\n'
text+='''theorem source (o : Openings) (s : Selectors)
 (hz : canonical o.z) (hs : canonical o.succ_z) (hx : canonical o.xor12_z)
 (hh : canonical s.high) (hl : canonical s.low) : run o s ⦃ l=>Canonical o l ⦄ := by
 have zero:=FIv_NativeValue.zero.1
 have zeros:=JFy_ZeroArrays.source 33#usize
 unfold run
 step*
 all_goals first | assumption | scalar_tac | (subst_vars;unfold Canonical;exact ⟨'''+','.join('by first|assumption|rfl' for _ in props)+'''⟩)
#print axioms source
end AspisR1.NKI_ValueTrace
end
'''
(E/'NKI_ValueTrace.lean').write_text(text)
(E/'NKI_VALUE_TRACE_PIN.json').write_text(json.dumps(dict(fields=fields,binds=[n for n,e in binds],domains=props,pure=pure,input_sha256=hashlib.sha256(s.encode()).hexdigest()),indent=2))
