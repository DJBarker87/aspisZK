exec(open('evidence/pv-mfb-20261029/PV_MF_trace.py').read().split('out=[]')[0])
co=c.load('COHORTS.json');ej={x['module'].replace('/','.'):x['resolution']['path'] for x in co['selected'] if x.get('resolution')}; index=collections.defaultdict(set)
for p,m in mods.items():
 for i in m['imports']:
  index[i['name']].update(i['candidates'])
results=[]
for r in rows:
 if r['recount9_status'] not in ['CLOSED-ON-CANDIDATE','RESTORED']:continue
 cs=r.get('closing_statement9');seen={};gaps=[];queue=[]
 if cs:queue=[(cs['module'],cs['path'],[cs['module']])]
 while queue:
  name,p,chain=queue.pop()
  if name in seen:continue
  seen[name]={'path':p,'chain':chain,'authority':'EJR' if name in ej else 'tracked'}
  for i in mods.get(p,{}).get('imports',[]):
   n=i['name'];poss=i['candidates'];q=ej.get(n)
   if not q:
    if len(poss)==1:q=poss[0]
    elif poss:gaps.append({'module':n,'chain':chain,'candidates':poss});continue
    else:continue
   if q not in mods:
    # source may have a .txt extension; record need to read its imports separately
    gaps.append({'module':n,'chain':chain,'selected':q});continue
   queue.append((n,q,chain+[n]))
 hits=[{'record':i+1,'path':t['path'],'chain':v['chain']} for i,t in enumerate(stale) for v in seen.values() if v['path']==t['path']]
 results.append({'id':r['id'],'closing':cs,'modules':seen,'gaps':gaps,'hits':hits})
(D/'resolved-traces.json').write_text(json.dumps(results,indent=2));print([(x['id'],len(x['modules']),len(x['gaps']),len(x['hits'])) for x in results]);print('HITS',sorted(set((x['id'],h['path']) for x in results for h in x['hits'])))
