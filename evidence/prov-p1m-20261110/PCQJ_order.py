import json,collections
P='../prov-p6t-20261110/'
S=json.load(open(P+'PCXE_ALL_STATUS.json'));R=json.load(open(P+'PCXE_ROW_TABLES.json'))
m=S['modules'];sb=R['splitB_module_to_reached_names']
rows=collections.defaultdict(set)
for row,mm in R['row_to_module_to_definitions'].items():
  for mod,dd in mm.items():
    for d in dd: rows[(mod,d)].add(row)
out=[]
for mod,names in sb.items():
  for n in names:
    r=m.get(mod,{}).get(n)
    if r and r['status']=='OPEN':
      rs=(r.get('open_reason') or '')
      cls='NOFRESH' if rs.startswith(('NO_FRESH_EMISSION','NOT_COVERED','no Lean equality record','NO_COMMON')) else 'OTHER'
      out.append(dict(module=mod,definition=n,reason=rs[:90],cls=cls,rows=len(rows[(mod,n)])))
out.sort(key=lambda x:(-x['rows'],x['module'],x['definition']))
json.dump(out,open('PCQJ_ORDERED_OPEN.json','w'),indent=0)
nf=[x for x in out if x['cls']=='NOFRESH']
print(len(out),len(nf))
h=nf[:len(nf)//2]
json.dump(h,open('PCQJ_FIRST_HALF.json','w'),indent=0)
c=collections.Counter(x['module'] for x in h)
for k,v in c.most_common(): print(v,k)
