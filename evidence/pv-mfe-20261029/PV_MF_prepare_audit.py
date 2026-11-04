from pathlib import Path
import json,lzma,subprocess,hashlib
D=Path(__file__).resolve().parent;j=json.load(open(D/'h5-input.json'));base=set(j['modules']);old=json.load(open(D/'jobs-h5.json'));own={m:j['modules'][m] for _,m in old};r=next(x for x in json.load(lzma.open(D/'resolved-traces.json.xz')) if x['id']=='V195');mods=r['modules'];order=[];seen=set();blocked=[]
def visit(m):
 if m in seen:return
 seen.add(m)
 if m in base:return
 if m not in mods:blocked.append(m);return
 for dep in mods[m]['imports']:visit(dep)
 order.append(['rebuild',m])
visit('R1Z.PV_Join_ClosureCheckpoint')
# The first 47 smallest dependencies are independent of the unresolved h7 imports.
chosen=order[:47];available=base.copy();accepted=[];deferred=[]
external={x['module'].replace('/','.') for x in json.load(open(D.parent/'pv-mfb-20261029/external-object-manifest.json'))}
for mode,m in order:
 if len(accepted)==47:break
 if not set(mods[m]['imports']) <= available|external:deferred.append(m);continue
 own[m]=mods[m];available.add(m);accepted.append([mode,m]);p=D/'audit-sources'/(m.replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);b=subprocess.check_output(['git','show','HEAD:'+mods[m]['path']]);assert hashlib.sha256(b).hexdigest()==mods[m]['sha256'];p.write_bytes(b)
j['modules']=own;(D/'h5-audit-input.json').write_text(json.dumps(j,indent=2)+'\n');(D/'jobs-audit.json').write_text(json.dumps(accepted,indent=2)+'\n');(D/'audit-frontier-plan.json').write_text(json.dumps(dict(target='R1Z.PV_Join_ClosureCheckpoint',scheduled=len(accepted),total_noncohort_dependencies=len(order),unresolved_imports=sorted(set(blocked)-external),deferred_due_to_unresolved_predecessors=deferred,remaining=[j for j in order if j not in accepted]),indent=2)+'\n');print('scheduled',len(accepted),'of',len(order),'noncohort dependencies; gaps',sorted(set(blocked)-external))
