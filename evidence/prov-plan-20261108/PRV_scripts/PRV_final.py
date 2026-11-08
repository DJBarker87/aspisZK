import json,collections,sys,re,subprocess
S=sys.argv[1]
o=json.load(open(f"{S}/classified.json"))
roots=json.load(open(f"{S}/roots.json"))
bm=json.load(open(f"{S}/blob_mods.json"))
inv={b['blob']:b for b in json.load(open("emission-repro-20261110/NMH_INVENTORY.json"))['blobs']}
nml={b['blob']:b for b in json.load(open("emission-repro2-20261110/NML_PROVENANCE.json"))['blobs']}
nmlin={b['blob']:b['source_status'] for b in json.load(open("emission-repro2-20261110/NML_INPUT_MAP.json"))['blobs']}
led=json.load(open(f"{S}/NNK_LEDGER.json"))
closed=sorted(r['row'] for r in led['rows'] if r['status']=='CLOSED')
FROZEN={'aspis_core','aspis_statement','aspis_r1_cost_probe','aspis_r1_cost_probe_program','aspis_pool'}
# frozen module paths
fmods=set()
for l in open(f"{S}/frozen_rs.txt"):
    p=l.strip().split('/src/',1)[1][:-3]
    parts=p.split('/')
    if parts[-1] in ('mod','lib'): parts=parts[:-1]
    for i in range(len(parts)): fmods.add('::'.join(parts[i:]))
def frozen_mappable(symn):
    p=re.sub(r'\{[^{}]*\}','',re.sub(r'\{[^{}]*\}','',symn)).replace('CRATE::','')
    parts=[x for x in p.split('::') if x]
    for k in range(len(parts)-1,0,-1):
        for i in range(k):
            if '::'.join(parts[i:k]) in fmods: return True
    return len(parts)<=1  # crate-root items (lib.rs) undecidable -> assume mappable
# rs files per job dir
rs_by_dir=collections.defaultdict(list)
for l in open(f"{S}/all_rs.tsv"):
    g,p=l.rstrip('\n').split('\t')
    parts=p.split('/')
    if 'evidence' in parts:
        i=parts.index('evidence'); rs_by_dir['/'.join(parts[:i+2])].append((g,p))
def jobdir(p):
    parts=p.split('/')
    if 'evidence' in parts: i=parts.index('evidence'); return '/'.join(parts[:i+2])
    return None
def ref_source(v):
    st=[c.get('nml_source_status') for c in v['candidates']]
    if any(s in ('RECOVERED_HASH_LINKED_INPUT','RECOVERED_LLBC_LINKED_PACKAGE') for s in st): return 'b1_committed_hash_linked'
    names=set()
    for n,d in v['defs'].items():
        last=re.sub(r'\{[^{}]*\}','',d['symn']).split('::')[-1]
        if last: names.add(last)
    found=False
    for c in v['candidates']:
        for p in c['paths']:
            jd=jobdir(p)
            if not jd: continue
            for g,rp in rs_by_dir.get(jd,[])[:400]:
                t=subprocess.run(['git','cat-file','-p',g],capture_output=True).stdout.decode('utf-8','replace')
                if any(re.search(r'\bfn\s+'+re.escape(n)+r'\b',t) for n in names): found=rp; break
            if found: break
        if found: break
    return ('b2_committed_not_linked:'+found) if found else 'b3_source_not_found'
mods={}
for m,v in o.items():
    rec={'module':m,'kind':v['kind'],'crates':v['crates'],'prov':v['prov'],'relied':v['relied'],'n_rows':len(v['rows']),'rows':v['rows'],
         'n_roots':len(v['roots']),'reached_emitted_defs':v['reached_emitted_defs'],'coverage':v['coverage'],'candidates':v['candidates']}
    if not v['relied']: g='d'; sub='d_no_CLOSED_root_reaches'
    elif v['prov']=='RECEIPTED': g='R'; sub='receipted_or_reproduced'
    elif v['prov']=='MIXED': g='a'; sub='a_pending_live_version_is_receipted_or_copy'
    elif v['kind']=='REFERENCE' and not (set(v['crates'])&FROZEN):
        g='b'; sub=ref_source(v)
    else:
        n=v['reached_emitted_defs']; cov=v['coverage']
        ident=cov.get('IDENTICAL',0)+cov.get('IDENTICAL_SOME_VERSION',0)
        if n>0 and ident==n: g='a'; sub='a_identical_to_fresh_frozen_receipted_emission'
        elif n==0: g='c'; sub='c0_no_annotated_definition_reached_manual_mapping'
        elif cov.get('UNCOVERED',0)==0: g='c'; sub='c1_extraction_exists_equality_needed'
        else: g='c'; sub='c2_new_extraction_and_equality'
        cut=[d for d in v['defs'].values() if d['cov']=='UNCOVERED' and not frozen_mappable(d['symn'])]
        rec['uncovered_not_frozen_mappable']=len(cut)
    rec['group']=g; rec['subgroup']=sub
    rec['defs']=v['defs']
    mods[m]=rec
# blob partition
blobs=[]
for b,ms in bm.items():
    m=ms[0]; r=mods.get(m)
    live=r and any(c['sha256']==b for c in r['candidates'])
    if r is None: g,sub='d','d_module_not_emitted_candidate'
    elif not r['relied']: g,sub='d','d_module_not_reached_by_CLOSED_root'
    elif not live: g,sub='d','d_superseded_version_not_compiled_into_gate'
    elif nml[b]['verdict'].startswith('REPRODUCED'): g,sub='a','a_reproduced_NMH_NML'
    else: g,sub=r['group'],r['subgroup']
    if g=='R': g,sub='a','a_module_live_version_receipted'
    blobs.append({'blob':b,'module':m,'group':g,'subgroup':sub,'nml_verdict':nml[b]['verdict'],'paths':inv[b]['paths'][:2],'module_rows':r['n_rows'] if r else 0})
summ={}
summ['blob_groups']=dict(collections.Counter(x['group'] for x in blobs))
summ['blob_subgroups']=dict(collections.Counter(x['subgroup'] for x in blobs))
summ['module_groups']=dict(collections.Counter(r['group'] for r in mods.values()))
summ['module_subgroups']=dict(collections.Counter(r['subgroup'] for r in mods.values()))
def rows_of(pred): return sorted(set(x for r in mods.values() if pred(r) for x in r['rows']))
R_c=rows_of(lambda r:r['group']=='c')
R_b3=rows_of(lambda r:r['subgroup']=='b3_source_not_found')
R_b2=rows_of(lambda r:r['subgroup'].startswith('b2'))
R_apend=rows_of(lambda r:r['subgroup']=='a_pending_live_version_is_receipted_or_copy')
R_atriv=rows_of(lambda r:r['subgroup']=='a_identical_to_fresh_frozen_receipted_emission')
R_any=rows_of(lambda r:r['relied'] and r['group']!='R')
summ['rows']={'closed':len(closed),'rootless':['TX1:059','TX2:040'],
 'any_unreceipted_emitted_module':len(R_any),
 'c':len(R_c),'c_or_b_unlinked':len(set(R_c)|set(R_b2)|set(R_b3)),
 'c_or_b_unlinked_or_a_pending':len(set(R_c)|set(R_b2)|set(R_b3)|set(R_apend)),
 'a_trivial_only':len(set(R_atriv)-set(R_c)-set(R_b2)-set(R_b3)-set(R_apend))}
summ['defs']={}
for g in ['c0_no_annotated_definition_reached_manual_mapping','c1_extraction_exists_equality_needed','c2_new_extraction_and_equality']:
    cv=collections.Counter()
    for r in mods.values():
        if r['subgroup']==g:
            for k,x in r['coverage'].items(): cv[k]+=x
    summ['defs'][g]=dict(cv)
summ['c_modules_uncovered_not_frozen_mappable']=sum(1 for r in mods.values() if r['group']=='c' and r.get('uncovered_not_frozen_mappable'))
json.dump({'summary':summ,'rows_c':R_c,'rows_c_or_b_unlinked_or_a_pending':sorted(set(R_c)|set(R_b2)|set(R_b3)|set(R_apend)),'modules':mods,'blobs':blobs},open(f"{S}/partition_full.json","w"),indent=0)
print(json.dumps(summ,indent=1))
