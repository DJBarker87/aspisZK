import json,collections
d=json.load(open('prov-p6r-20261110/PCXD_EXTERNALS.json'))['c']
def crate(n):
    if n.startswith(('core.','alloc.','std.')): return 'core_alloc_std'
    if n.startswith('solana_'): return 'solana'
    return 'aspis_frozen'
def row(n):
    if n.startswith('solana_'): return 'HM-A (accepted SDK row)'
    if n.startswith('core.slice.Slice') or 'SliceIndex' in n: return 'HM-D'
    if n.startswith('core.'): return 'HM-F'
    return None
out=[];
for r in d:
    c=crate(r['name']);out.append({'gate_module':r['gate_module'],'name':r['name'],'crate':c,'row':row(r['name']) if c!='aspis_frozen' else None,'status':'LIBRARY_TRUST' if c!='aspis_frozen' else 'OPEN_OBLIGATION'})
cnt=collections.Counter(o['crate'] for o in out)
dist=collections.defaultdict(set)
for o in out: dist[o['crate']].add(o['name'])
rows=collections.Counter(o['row'] for o in out if o['row'])
res={'schema':'PCVG_EXTERNALS_BY_CRATE/1','target_established':False,'source':'prov-p6r-20261110/PCXD_EXTERNALS.json section c','n':len(out),
 'counts_entries':dict(cnt),'counts_distinct_names':{k:len(v) for k,v in dist.items()},'entries_by_row':dict(rows),
 'rule':'crate by name prefix: core./alloc./std. -> core_alloc_std; solana_ -> solana; everything else (aspis_*, r1_*, compact., multiproof., verifier., ...) -> aspis_frozen, kept as OPEN_OBLIGATION. No row added to any document.',
 'entries':out}
json.dump(res,open('prov-p3g-20261110/PCVG_EXTERNALS_BY_CRATE.json','w'),indent=1)
print(res['counts_entries'],res['counts_distinct_names'],res['entries_by_row'])
