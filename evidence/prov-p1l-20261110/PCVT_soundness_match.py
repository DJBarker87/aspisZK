import json,glob,os,re,sys
ev='..'
pf=json.load(open('/private/tmp/claude-501/s/pf.json'))['items']
xe=json.load(open(ev+'/prov-p6t-20261110/PCXE_ALL_STATUS.json'))['modules']
xd=json.load(open(ev+'/prov-p6r-20261110/PCXD_PROVENANCE.json'))['modules']
items=[i for i in pf if i['soundness_original_build_exit0_root']]
def runinfo(run):
    g=glob.glob(f'{ev}/*/{run}_spec.json')[0]; d=os.path.dirname(g)
    sp=json.load(open(g)); ar=json.load(open(f'{d}/{run}_emitted/aeneas_receipt.json'))
    pins=f'{d}/{run}_emitted/{run}_PINS.json'
    c=sp['configuration']
    return {'run':run,'spec':g[3:],'pins':pins[3:] if os.path.exists(pins) else None,'aeneas_exit':ar['exit'],'tool_sha256':ar['tool_sha256'],'tool_path':ar['command'][0],'aeneas_source_revision_in_receipt':ar.get('source_revision'),'namespace':c.get('namespace'),'crate':c.get('crate'),'features':c.get('features'),'overflow_env':sp.get('extra_env'),'frozen_revision':sp.get('frozen_revision'),'start_from':c.get('start_from'),'opaque':c.get('opaque')}
def prefixes(name):
    p=name.split('::')
    if name.endswith('weights::{impl}::raw::{impl}::call_mut'): return ['FIo_Native.weights.Weights.raw']
    if name.endswith('copy_terminal::{impl}::active_literal'): return ['FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors.active_literal']
    if name.endswith('copy_terminal::{impl}::expand'): return ['FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors.expand']
    if 'absorption_lanes_literal' in name: return ['FIq_Native.pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal']
    return ['FIq_Native.'+'.'.join(p[1:])]
out=[]
for i in items:
    pre=prefixes(i['name']); defs=[]
    for mk,mv in xe.items():
        for dn,dv in mv.items():
            if any(dn.startswith(p) and re.fullmatch(r'(_loop\d*)*(\.(body|closure(_\d+)?))*(\.(body|closure(_\d+)?))?',dn[len(p):]) for p in pre):
                dd=xd.get(mk,{}).get('definitions',{}).get(dn,{})
                defs.append({'constant':dn,'module':mk,'pcxe_status':dv['status'],'open_reason':dv.get('open_reason'),'configuration':dv.get('configuration'),'theorem':dv.get('theorem'),'proving_file':dv.get('proving_file'),'receipt':dv.get('receipt'),'fresh_emission':dv.get('fresh_emission'),'aeneas_tool':dv.get('aeneas_tool'),'decided_by':dv.get('decided_by'),'pcxd_status':dd.get('status')})
    runs=[runinfo(r) for r in i['soundness_original_build_exit0_root']]
    cnt={}
    for d in defs: cnt[d['pcxe_status']]=cnt.get(d['pcxe_status'],0)+1
    prim=[d for d in defs if d['constant'] in pre] or defs[:1]
    out.append({'item':i['name'],'file':i['file'],'line':i['line'],'stream_b_error_class':i['error_class'][:60],'gate_constants_prefix':pre,'primary_constant':prim[0]['constant'] if prim else None,'primary_status':prim[0]['pcxe_status'] if prim else None,'n_related_constants':len(defs),'status_counts':cnt,'constants':defs,'emission_runs':runs,'source':'frozen 4bb3b3f (emission staged from frozen payload; spec frozen_revision)','verdict':'EXISTING_GATE_CONSTANT'})
json.dump({'schema':'PCVT_SOUNDNESS_MATCH/1','target_established':False,'note':'18 items where a soundness original-build (959659a6) run exited 0 with the item Structured. Statuses copied as recorded in PCXE_ALL_STATUS.json (P6t) with the P6r PCXD per-definition status alongside. No new proof.','items':out},open('PCVT_SOUNDNESS_MATCH.json','w'),indent=1)
for o in out: print(o['item'].split('::',1)[1][:70],o['n_related_constants'],o['status_counts'],[r['run'] for r in o['emission_runs']],o['primary_status'])
