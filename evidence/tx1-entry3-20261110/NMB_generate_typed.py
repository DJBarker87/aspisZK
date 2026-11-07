"""Annotate the committed NLD source with explicit typed live environments.
No extractor or source/model change. Generated body erases to NLD exactly.
"""
from pathlib import Path
import re,json,hashlib,sys
E=Path(__file__).resolve().parent
p=E.parent/'tx1-entry-20261109/NLD_Stage1Source.lean'
s=p.read_text();body=s[s.index('def stage1Owned'):s.index('\ntheorem erasure')]
body=body.replace('  Trace (','  Run (')
body=re.sub(r'\bpure\b','NMB_TypedTrace.pure',body)
stack=[(-1,n)for n in ['program_id','accounts','data']];out=[];sites=[]
for line in body.splitlines(True):
 text=line.strip();indent=len(line)-len(line.lstrip())
 statement=bool(re.match(r'(let |if |then$|else$|match |\||pure |call |=>$)',text))
 if statement:stack=[(level,name)for level,name in stack if level<=indent]
 pattern=re.match(r'\|.*\.?(?:Continue|Break)\s+(\w+)\s*(?:=>)?$',text)
 if pattern and pattern.group(1)!='_':stack.append((indent+1,pattern.group(1)))
 call=re.search(r'\bcall (\d+) \(',line)
 if call:
  names=list(dict.fromkeys(name for _,name in stack));env='['+','.join('('+json.dumps(name)+',pack '+name+')' for name in names)+']'
  line=line[:call.start()]+line[call.start():].replace('call '+call.group(1)+' (','call '+call.group(1)+' '+env+' (',1)
  sites.append(dict(site=int(call.group(1)),names=names))
 out.append(line)
 binder=re.match(r'let\s+(\w+)\s*(?:←|:=)',text)
 if binder:stack.append((indent,binder.group(1)))
header='''import NMB_TypedCongr
import NLD_Stage1Source
set_option autoImplicit false
noncomputable section
namespace NMB_OwnedTyped
open Aeneas Aeneas.Std Result NMB_TypedTrace NMB_TypedControl
open _root_.AdapterRw
/-- NLD's COMPLETE emitted source, with full nominal replies and live values.
Ops is explicit source configuration, not hidden in environment or a row root.
This is SOURCE instrumentation only; full native child packets remain open. -/
'''
footer='''
attribute [local irreducible] NMB_TypedTrace.forget NMB_TypedTrace.bind NMB_TypedTrace.pure NMB_TypedTrace.call
theorem forget_eq (ops : AdapterRw.Ops) (program : AdapterRw.solana_pubkey.Pubkey)
 (accounts : Slice AdapterRw.r1_pool_adapter.owned.OwnedAccount) (data : Slice U8) :
 forget (stage1Owned ops program accounts data)=
 AspisR1.NLD_Stage1Source.stage1Owned ops program accounts data := by
 unfold stage1Owned AspisR1.NLD_Stage1Source.stage1Owned
 all_goals repeat' first
  | (with_reducible rfl)
  | (apply forget_call)
  | (apply forget_pure)
  | (apply NMB_TypedCongr.bind_congr)
  | (apply NMB_TypedCongr.ite_congr)
  | (apply NMB_TypedCongr.control_congr)
  | intro x
  | cases x
#print forget_eq
#print axioms forget_eq
end NMB_OwnedTyped
'''
rendered=header+''.join(out)+footer
manifest=dict(source=str(p.relative_to(E.parent.parent)),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),generated_sha256=hashlib.sha256(rendered.encode()).hexdigest(),sites=sites,source_only=True,root_credit=False)
target=E/'NMB_OwnedTyped.lean';mp=E/'NMB_TYPED_SOURCE.json'
if '--check'in sys.argv:
 assert target.read_text()==rendered and json.loads(mp.read_text())==manifest
 print('NMB typed source manifest validated')
else:
 target.write_text(rendered);mp.write_text(json.dumps(manifest,indent=1)+'\n');print('NMB typed source generated: '+str(len(sites))+' occurrences')
