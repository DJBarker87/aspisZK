from pathlib import Path
import runpy,json,collections
E=Path(__file__).resolve().parent;d=runpy.run_path(str(E/'prepare-formal.py'));R=d['R'];resolution=d['resolution'];imports=d['imports']
groups={'CB':'R1Z.PV_CB_CandidateDictionary','CB3':'R1Z.PV_CB3_CallbackBundle','CBM':'R1Z.PV_CBM_CallbackBundle','Op134':'R1Z.PV_Op134_ReferenceBundle','CBL':'R1Z.PV_CBL_CallbackPublication','Join':'R1Z.PV_Join_AggregateCaller','L2B':'PV_L2B_JointTransport','Op223':'R1Z.PV_Op223_Source'}
roots=['R1Z.PV_Op223_V164','R1Z.PV_Join_AggregateCaller','R1Z.PV_Join_PublicCaller','R1Z.PrivacyR1HeadlineDeployedReal'];result=[]
for root in roots:
 q=collections.deque([(root,[root])]);seen=set();paths={}
 while q:
  n,path=q.popleft()
  if n in seen:continue
  seen.add(n);paths[n]=path
  if n not in resolution or not (R/resolution[n]).is_file():continue
  for m in imports((R/resolution[n]).read_text()):q.append((m,path+[m]))
 result.append(dict(consumer=root,publication_paths={k:paths.get(v) for k,v in groups.items()},callback_source_examples={prefix:next((paths[n] for n in paths if n.startswith(prefix)),None) for prefix in ['R1Z.PV_CB_','R1Z.PV_CB3_','R1Z.PV_CBL_','R1Z.PV_CBM_','PV_L2B_']},visited=len(seen),meaning='null means no source-import path; audit presence is not consumer adoption'))
(E/'consumer-paths.json').write_text(json.dumps(result,indent=2)+'\n')
for r in result:print(r['consumer'],{k:bool(v) for k,v in r['publication_paths'].items()})
