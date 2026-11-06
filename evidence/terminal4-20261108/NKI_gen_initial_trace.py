from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent;s=(E/'NKI_InitialPrefix.lean').read_text();body=s[s.index(' : Result Tail := do')+len(' : Result Tail := do'):s.index('  ok ⟨initial2')]
parts=re.split(r'^  let ',body,flags=re.M)[1:];fields=[]
for part in parts:
 name,expr=part.split(' ←',1)
 for n in [x.strip() for x in name.strip().strip('()').split(',')]:
  ty='NQ'
  if n=='s':ty='Slice'
  elif n in ['full','full_or_rate']:ty='NP'
  elif n in ['initial','initial1','initial2']:ty='Array'
  elif n=='i':ty='Usize'
  fields.append((n,ty))
head='''import NKI_InitialInvocation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_InitialTrace
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open NKI_InitialPrefix (Public Openings Selectors)
open NKI_InitialInvocation (Locals)
'''
text=head+'def run (public1 : Public) (openings : Openings) (selectors : Selectors) : Result Locals := do\n'+body+'  ok ⟨'+','.join(n for n,_ in fields)+'⟩\n'
canon=[]
for n,ty in fields:
 if ty=='NQ':canon.append('Canon l.'+n)
 elif ty=='Array':canon.append('canonical l.'+n)
 elif ty=='NP':canon.append('JFy_PreparedSteps.Valid l.'+n)
text+='def Canonical (l : Locals) : Prop :=\n '+' ∧\n '.join(canon)+'\n'
text+='''/-- All actual intermediate domains are returned, for later native cut
instantiation. No scalar, cache or array domain is an extra root premise. -/
theorem source (p : Public) (o : Openings) (s : Selectors)
 (hz : canonical o.z) (hh : canonical s.high) (hl : canonical s.low) :
 run p o s ⦃ l=>Canonical l ⦄ := by
 have zero:=FIv_NativeValue.zero.1
 unfold run poseidon2.RATE
 step*
 all_goals first
  | (subst_vars;exact FIx_ScheduleIndices.node_bounds)
  | (unfold Canonical;exact ⟨'''+','.join('by assumption' for _ in canon)+'''⟩)
#print axioms source
end AspisR1.NKI_InitialTrace
end
'''
(E/'NKI_InitialTrace.lean').write_text(text)
(E/'NKI_INITIAL_TRACE_PIN.json').write_text(json.dumps(dict(input_sha256=hashlib.sha256(s.encode()).hexdigest(),fields=len(fields),domains=len(canon),change='Same58bindprefix; return all61locals to expose every actual intermediate domain'),indent=2))
