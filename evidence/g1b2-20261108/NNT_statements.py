"""Record complete source statements and check the authorised interface edits."""
from pathlib import Path
import re,subprocess,json,hashlib
E=Path(__file__).resolve().parent
mapping={
 'NNT_TopLCore':('evidence/top-assembly-20261107/TAS_Top.lean',{}),
 'NNT_TopLEvent':('evidence/event-b-20261107/EVB_EventB.lean',{'event_top_splitB':'top_splitB','event_top_splitB_full':'top_splitB_full'}),
 'NNT_TopLB':('evidence/top-assembly-20261107/TAS_TopB.lean',{}),
 'NNT_TopL':('evidence/top-assembly-20261107/TAS_TopB_NNE.lean',{'selected_top_split':'top_split'})}
def statement(s,n):
 m=re.search(r'^theorem '+n+r'\b',s,re.M);assert m,n
 return s[m.start():].split(':=',1)[0].strip()
def normal(s):
 s=re.sub(r'/\-.*?\-/','',s,flags=re.S);s=re.sub(r'--[^\n]*','',s)
 return ' '.join(s.split())
def edits(s):
 return s.replace('NMS_Roots ','NMS_RootsL ').replace('NNC_G1a ','NNC_G1aL ').replace('Refines064 V0 I.f064 R0 w','LawRefines V0 R0 w').replace(' (nmn : NMN_Root L V0 VL I)','')
out=['# Full before/after consumer statements','Only the authorised structure/premise edits and unused nmn removal apply. NMF and case-split structures have their full unchanged fields re-expressed over the new G1a carrier in NNT_TopL. No adversary, carrier, event or conclusion is specialised.']
rows=[]
for module,(source,renames) in mapping.items():
 s=(E/(module+'.lean')).read_text()
 for n in re.findall(r'^theorem (\w+)',s,re.M):
  path='evidence/phys-adapter-20261111/NNE_TopSplit.lean' if n=='selected_top_split' else source
  old=subprocess.check_output(['git','show','HEAD:'+path],text=True)
  before=statement(old,renames.get(n,n));after=statement(s,n)
  expected=edits(before).replace('theorem '+renames.get(n,n),'theorem '+n,1)
  assert normal(expected)==normal(after),(module,n)
  out+=['\n## '+module+'.'+n,'Before (`'+path+'`):','```lean',before,'```','After:','```lean',after,'```']
  rows.append(dict(module=module,theorem='NNT_TopL.'+n,source=path,source_sha256=hashlib.sha256(old.encode()).hexdigest(),statement_edit_check=True))
(E/'NNT_STATEMENTS.md').write_text('\n'.join(out)+'\n')
(E/'NNT_STATEMENT_CHECK.json').write_text(json.dumps(rows,indent=2)+'\n')
print(len(rows),'complete statements checked')
