from pathlib import Path
import hashlib,json,subprocess
L=Path('evidence/pv-lib-20261107/lane-SPEC')
rows=[361,270,166,15,208,220,316,318,219,125,6,170,17,5,2,1,0,'OwnInit']
ids={361:49747,270:49752,166:49753,15:49750,208:49755,220:49756,316:49777,318:49758,219:49759,125:49760,6:49761,170:49762,17:49765,5:49767,2:49769,1:49771,0:49772,'OwnInit':49773}
index=json.loads((L/'CONTRACT_INDEX.json').read_text())
index.update(session=5,thread_scope=18,whole_operational_statements_compiled=18,full_frozen_contracts=0,composition_witness_statement_compiled=True,composition_witness_inhabited=False)
for row in index['rows']:
 key=row['row'].split(':')[-1]
 n='OwnInit' if key=='OwnInit' else int(key[1:]) if key.startswith('f') else None
 if not row['row'].startswith('thread:') or n not in rows:
  row['current_lane']='B (slice/source7)' if row['row'].startswith('slice:') else 'historic'
  continue
 ns='PV_LIB_SPEC_F316Callback' if n==316 else 'PV_LIB_SPEC_Frozen.'+('OwnInit' if n=='OwnInit' else 'F'+str(n))
 module='PV_LIB_SPEC_F316Callback' if n==316 else 'PV_LIB_SPEC_ThreadSpecifications'
 row.update(whole_operational_statement_compiled=True,full_frozen_contract_elaborated=False,
    statement_component=ns+'.Contract',comparison_component=ns+'.Comparison',
    whole_fields={field:ns+'.'+field for field in ['Pre','Post','MachineSpec','Contract']},
    authoritative_module='lean/'+module+'.lean',
    row_compile=ids[n],final_common_compile=49777 if n==316 else 49774,
    comparison_status='compiled propositions paired with pinned package statements; no equivalence/transport proof',
    remaining='Full named leaf/ABI/resource bindings and source adequacy are not established by reference execution. No row proof.')
(L/'CONTRACT_INDEX.json').write_text(json.dumps(index,indent=2)+'\n')
delta=json.loads((L/'MAP_DELTA.json').read_text())
delta.update(session=5,thread_scope=18,whole_operational_statements_compiled=18,full_frozen_contracts=0,proved_rows=0,endpoint_premises_removed=0)
delta['session5_slots']=[{'slot':'thread:'+('OwnInit' if n=='OwnInit' else 'f'+str(n)),
  'statement':('PV_LIB_SPEC_F316Callback' if n==316 else 'PV_LIB_SPEC_Frozen.'+('OwnInit' if n=='OwnInit' else 'F'+str(n)))+'.Contract',
  'status':'STATEMENT-ONLY; SOURCE-ADEQUACY-OPEN','row_compile':ids[n]} for n in rows]
(L/'MAP_DELTA.json').write_text(json.dumps(delta,indent=2)+'\n')
status={'base':'f2798a4fac4380ce34d387a483bd7e461f707eac','branch':subprocess.check_output(['git','branch','--show-current'],text=True).strip(),
 'correction':'D984 accepted SPEC-C3; full table remains lane A parameter',
 'whole_operational_statements':18,'full_frozen_source_adequacy_claimed':False,'row_proofs':0,
 'ownInit_composition_statement':'PV_LIB_SPEC_OwnInitComposition.Witness',
 'joint_witness_inhabited':False,'endpoint_premises_removed':0,'source7_scope':'lane B',
 'unused_lean_ids':[49748,49749]+list(range(49782,49790)),'next_raw':49796,
 'remaining':['Named native value, resource and OWNER/heap footprint facts must be connected to actual source leaves; Frozen.runtime currently lifts a backend-only handler.',
 'Physical typed-reference/ABI validity and mutable/disjoint byte footprints must be bound to source addresses, beyond readable source cells and registered descriptors.',
 'ResourceBinding is a target, not an established site/occurrence association.',
 'Completed table must be supplied by lane A with all D984 writes and symbolic away agreement.',
 'OwnInitComposition.Witness is an unproved joint realization target including all contracts. It is NOT a concrete witness of the actual composed premises and does not discharge joint nonemptiness.',
 'Actual continuous original-entry callback/register/decode14756 allocation trace and allBridged/SourceInitBoxOwnership application remain open.',
 'Paired comparison propositions do not establish old/new equivalence or provider graph adapters.']}
# Pin exactly changed own logical sources, omitting runtime metadata/audit tools.
changed=subprocess.check_output(['git','diff','--name-only','f2798a4fac4','HEAD'],text=True).splitlines()
status['sources']={f:hashlib.sha256(Path(f).read_bytes()).hexdigest() for f in changed if f.startswith('lean/PV_LIB_SPEC_') and 'RawAudit' not in f and 'CohortImports' not in f}
if (L/'SESSION5_RAW_AUDIT.json').exists():status['raw_audit']=json.loads((L/'SESSION5_RAW_AUDIT.json').read_text())
(L/'SESSION5_STATUS.json').write_text(json.dumps(status,indent=2)+'\n')
(L/'SESSION5_COMMITS.txt').write_text(subprocess.check_output(['git','log','--format=%H %s','f2798a4fac4..HEAD'],text=True))
