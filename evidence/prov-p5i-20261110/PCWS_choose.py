import json,collections,re,glob
fc=json.load(open('/tmp/pcxl_classes.json'))['final_class']
tri=json.load(open('prov-p5a-20261110/PCWJ_TRIAGE.json'))
rec={(r['module']+'|'+r['definition']):r for r in tri['records']}
excl_pre=('RPu_FIq_Native','AspisR1Post25Sampler.Funs','RPz7_WAdm_Fissioned','S8OwnedP6','OraclePortCkptAbi2','S1ValuesOwnedModelV1','AspisR1Qm31SamplerIndex','AdapterRwModel','NCV_','NCX_','NEG_','NGD_')
ce=''
for f in glob.glob('prov-p1j-*/PCVJ_CANNOT_EXTRACT.json')+glob.glob('prov-p1k-*/PCVR_CANNOT_EXTRACT.json')+glob.glob('prov-p3t-*/PCVV_CANNOT_EXTRACT.json')+glob.glob('prov-p3u-*/PCVX_CANNOT_EXTRACT.json')+glob.glob('prov-p4y-*/PCWO_CANNOT_EXTRACT.json')+glob.glob('prov-p5[cde]-*/*REMAINING.json'):
    ce+=open(f).read()
bym=collections.defaultdict(list)
for k,v in fc.items():
    if v!='OPEN': continue
    m=k.split('|')[0]
    if m.startswith(excl_pre): continue
    bym[m].append(k)
out=[]
for m,ks in sorted(bym.items(), key=lambda x:-len(x[1])):
    c=collections.Counter(rec[k]['cause'] if k in rec else 'NOTRIAGE' for k in ks)
    out.append((m,len(ks),dict(c), m in ce))
json.dump(out,open('prov-p5i-20261110/PCWS_candidates.json','w'),indent=1)
for o in out: 
    if not o[3]: print(o)
