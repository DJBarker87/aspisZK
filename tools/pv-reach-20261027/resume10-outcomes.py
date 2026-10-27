"""Failure/divergence of each actual client effect prefix, no whole-client success premise."""
from pathlib import Path
import re
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
for family,count in [('Store',12),('After',8)]:
 for i in range(count):
  base=f'PV_RE_Client{family}10{i:02d}';src=(L/(base+'.lean')).read_text()
  lead=src.split('theorem prefix',1)[0].replace('namespace R1Z.'+base,'namespace R1Z.'+base+'Outcomes')
  lead='import R1Z.'+base+'\n'+lead[lead.index('set_option'):]
  args=src.split('theorem prefix',1)[1].split(' :\n    letI',1)[0]
  tail=src.split('    letI : ExternalFuns := ProverRwOuterMapErr.selected ops\n',1)[1].split(' := by',1)[0]
  ext=''
  if tail.startswith('    ∀ '):ext=tail[6:tail.index(',\n    ∃ next')];tail=tail[tail.index('    ∃ next'):]
  match=re.search(r'∃ next, (.*?) = \((.*) >>= next\)',tail,re.S);whole=match[1];call=match[2]
  ordered=[]
  if ext:
   for name in re.findall(r'\((\w+)\s*:',ext):ordered.append(name)
  # Prefix binders are source ordered, and all of these occur exactly once.
  common='ops entropy pub compiled hash store state state1 secret entropy_prefix bytes digest serialization first_hash second_hash'
  invoke=base+'.prefix '+common+' '+' '.join(ordered)
  text=lead
  for name,res,hyp in [('failure','.fail e',f'(e : Error) (stopped : {call} = .fail e)'),('divergence','.div',f'(stopped : {call} = .div)')]:
   text+='theorem '+name+args+' :\n    letI : ExternalFuns := ProverRwOuterMapErr.selected ops\n'
   binders=ext+' '+hyp
   text+='    ∀ '+binders+',\n    '+whole+' = '+res+' := by\n'
   text+='  letI : ExternalFuns := ProverRwOuterMapErr.selected ops\n'
   text+='  intro '+' '.join(ordered+(['e'] if name=='failure' else [])+['stopped'])+'\n'
   text+=f'  obtain ⟨next,hn⟩ := {invoke}\n  rw [stopped] at hn\n  exact hn\n#print axioms {name}\n'
  text+='end R1Z.'+base+'Outcomes\n'
  (L/(base+'Outcomes.lean')).write_text(text)
