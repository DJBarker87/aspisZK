from pathlib import Path
import json,re,hashlib,statistics
P=Path('docs/research/100bit-spend-path-20261013/evidence/decision1h-rollover-measurements-20261019')
VERIFIER='7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue'
POOL='5PjDJaGfSPJj4tFzMRCiuuAasKg5n8dJKXKenhuwZexx'
ELF='4e1fd78fbddb39cb9599de7694105547d8e86e7451f8b9f3e9626789036e8711'
def consumed(logs,program):
    rows=[]
    for line in logs:
        m=re.fullmatch(r'Program '+re.escape(program)+r' consumed (\d+) of (\d+) compute units',line)
        if m:rows.append({'consumed':int(m[1]),'supplied_budget':int(m[2]),'raw':line})
    assert len(rows)==1,(program,rows)
    return rows[0]
def markers(logs,start):
    pending=None;out=[];previous='entry';remaining=start
    for i,line in enumerate(logs):
        if line.startswith('Program log: r1:'):pending=line.split('r1:',1)[1]
        m=re.fullmatch(r'Program consumption: (\d+) units remaining',line)
        if m and pending is not None:
            new=int(m[1]);out.append({'from':previous,'to':pending,'cost':remaining-new,'remaining':new,'log_line_1based':i+1});previous=pending;remaining=new;pending=None
    return out
rows=[]
for f in sorted((P/'results').glob('*-evidence.json')):
    d=json.loads(f.read_text());x=d['execution'];name=f.name.removesuffix('-evidence.json');op,count=name.split('-');count=int(count)
    assert d['artifacts']['r1_cost_probe_verifier']['sha256']==ELF
    assert x['declared_compute_unit_limit']==1400000 and not x['runtime_limit_is_diagnostic_override']
    assert x['error']is None and x['stage1_error']is None and x['simulation_equals_execution']and x['stage1_simulation_equals_execution']
    sl=x['stage1_logs'];pl=x['logs'];si=consumed(sl,VERIFIER);vi=consumed(pl,VERIFIER);pi=consumed(pl,POOL)
    sm=markers(sl,si['supplied_budget']);pm=markers(pl,vi['supplied_budget'])
    costs={r['to']:r['cost']for r in sm};pcosts={r['to']:r['cost']for r in pm}
    assert [int(r['to'].split(':')[1])for r in sm if r['to'].startswith('query:')]==list(range(10))
    assert [int(r['to'].split(':')[1])for r in pm if r['to'].startswith('query:')]==list(range(10,22))
    q9=costs['merkle:9']+costs['query:9']
    setup={k:{'compute_units':v['compute_units'],'error':v.get('error'),'logs':v.get('logs',[])}for k,v in d['registry_v2_governance'].items()if isinstance(v,dict)and'compute_units'in v}
    r={'case':name,'operation':op,'populated_pairs':count,'history_mode':d['authenticated_path']['history_mode'],'fixture':d['fixture'],
       'verifier_elf_sha256':ELF,'source_revision':'32559d2696b89cdbd75304c1f7624f94dfe125ae',
       'runtime_receipt':'runs/'+name+'-measure1/receipt.json','runtime_command':'runs/'+name+'-measure1/command.json',
       'stage1':{'transaction_cu':x['stage1_compute_units'],'invoked_verifier':si,'transaction_minus_invoked_verifier':x['stage1_compute_units']-si['consumed'],'headroom_1400000':1400000-x['stage1_compute_units'],'required_savings_for_1300000':max(0,x['stage1_compute_units']-1300000),'phase_intervals':sm,'after_last_marker_to_verifier_return':si['consumed']-sum(r['cost']for r in sm)},
       'settlement':{'transaction_cu':x['compute_units'],'invoked_pool':pi,'nested_invoked_verifier':vi,'pool_inclusive_minus_nested_verifier':pi['consumed']-vi['consumed'],'transaction_minus_nested_verifier':x['compute_units']-vi['consumed'],'transaction_minus_invoked_pool':x['compute_units']-pi['consumed'],'headroom_1400000':1400000-x['compute_units'],'required_savings_for_1300000':max(0,x['compute_units']-1300000),'nested_verifier_phase_intervals':pm,'after_last_marker_to_verifier_return':vi['consumed']-sum(r['cost']for r in pm),'all_program_consumption_lines':[s for s in pl if re.fullmatch(r'Program .* consumed \d+ of \d+ compute units',s)]},
       'source_query9_cost':{'merkle9':costs['merkle:9'],'evaluation9':costs['query:9'],'combined_marker_interval':q9,'geometry_increment_estimate':800,'geometry_estimate_status':'UNMEASURED rough allocation: first Merkle interval includes all batch geometry plus one path; 800 CU/query is a proposal estimate, not isolated timing.'},
       'unexecuted_9_13_split_estimate':{'status':'NOT EXECUTED. k9 is not admitted and driver has no split CLI. Arithmetic cost projection only.','stage1_excluding_geometry_change':x['stage1_compute_units']-q9,'settlement_excluding_geometry_change':x['compute_units']+q9,'stage1_with_800_geometry_estimate':x['stage1_compute_units']-q9-800,'settlement_with_800_geometry_estimate':x['compute_units']+q9+800,'additional_unmeasured_effects':['batch geometry range/allocation and fixed inversion','first-path/cache effects for query9 moved to stage2','observer/phase boundaries, serialization and checkpoint accumulator contents']},
       'combined_counted_transaction_CU':x['stage1_compute_units']+x['compute_units'],'combined_required_savings_for_two_1300000_caps':max(0,x['stage1_compute_units']+x['compute_units']-2600000),
       'setup_and_existing_driver_check_transactions':setup,'setup_transactions_excluded_from_two_counted_transactions':True,'state_checks':d['atomicity'],'acceptance':{'stage1':True,'actual_pool_settlement':True,'selected_verifier_cpi_observed':x['selected_verifier_cpi_observed_in_logs']}}
    rows.append(r)
(P/'phase-costs.json').write_text(json.dumps({'rows':rows,'interpretation':{'phase_costs':'Exact differences of existing Program consumption marks, inclusive of logging boundary overhead. They are intervals, not intrinsic operation costs.','stage1_entry_to_parsed':'Includes Pool adapter account/state checks, public decoding and View parsing; cannot isolate pure parse.','semantic':'Parsed→Semantic interval includes actual semantic work and marker cost.','prepare':'Semantic→Prepare includes Prepared::new, Accumulator initialization and gamma powers; cannot isolate components.','first_merkle':'Includes QueryGeometry::for_range for all queries in that transaction plus first Merkle path; later Merkle intervals exclude that setup.','checkpoint_read':'Parsed→CheckpointRead includes checkpoint decoding/hash checks and gamma powers.','pool_overhead':'Pool inclusive invoked CU minus nested verifier CU. Includes Pool work, history rollover, CPI invocation and possible Token CPI; existing marks do not split exact pre/post components.','measurement_metrics':'Per transaction CU is recorded; wall/RSS/swap belong to the encompassing process receipt, not separate per-transaction process measurements.'}},indent=2)+'\n')
for r in rows:print(r['case'],r['stage1']['transaction_cu'],r['settlement']['transaction_cu'],'nested',r['settlement']['nested_invoked_verifier']['consumed'],'pooloverhead',r['settlement']['transaction_minus_nested_verifier'],'q9',r['source_query9_cost'],'combinedgap',r['combined_required_savings_for_two_1300000_caps'])
