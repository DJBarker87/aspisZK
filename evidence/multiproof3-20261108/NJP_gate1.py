"""Own first combined gate; no authoritative ledger mutation."""
from pathlib import Path
import json,lzma,hashlib
E=Path(__file__).resolve().parent
read=lambda p:p.read_text() if p.exists() else lzma.open(str(p)+'.xz').read().decode()
roots=json.load(open(E/'NJP_AUDIT_ROOTS.json'))['roots']
for a in ['NJP_L024','NJP_L025','NJP_L026','NJP_L027']:
 r=json.load(open(E/a/'receipt.json'));assert r['exit_status']==0,a
 ad=json.load(open(E/(a+'-admission.json')));assert ad['exit']==0 and ad['reservation']['allowed'] is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert str(r['swaps'])=='0'
raw=[json.loads(l[11:]) for l in read(E/'NJP_L027/stdout.log').splitlines() if l.startswith('NEP_RESULT ')]
assert sorted(x['root'] for x in raw)==sorted(roots)
assert all(x['equal'] and set(x['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for x in raw)
fixtures=[json.loads(l[11:]) for l in read(E/'NJP_L024/stdout.log').splitlines() if l.startswith('NEP_RESULT ')]
assert len(fixtures)==8 and all(x['equal'] for x in fixtures)
assert all(x['walked_axioms'] for x in fixtures[:4]) and all(not x['walked_axioms'] for x in fixtures[4:])
scan=[json.loads(l) for l in read(E/'NJP_LOADED_scan.jsonl').splitlines()]
assert scan and all(not x['dangling'] and not x['duplicate_owners'] and x['imports_match'] for x in scan)
KMX='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
own_pairs=[['NJP_K006','NJP_K007'],['NJP_K008','NJP_K009'],['NJP_K057','NJP_K058'],['NJP_K057','NJP_K059']]
inherited=[['NJA_K121','NJA_K106'],['NJA_K107','NJA_K108'],['NJA_K109','NJA_K110'],['NJA_K111','NJA_K112'],['NJA_K113','NJA_K114']]
closed_pre=json.load(open(E.parent/'multiproof2-20261107/NJE_CLOSED.json'))
children=[f for f in closed_pre['functions'] if f['rows'][0] in ['TX1:302','TX1:303','TX1:304','TX1:307']]
for c in children:
 for pair in c['native_pairs']:
  if pair not in inherited:inherited.append(pair)
pins={}
for pair in own_pairs+inherited:
 for a,expected in [(pair[0],0),(pair[1],1)]:
  D=E if a.startswith('NJP') else E.parent/('multiproof2-20261107' if a.startswith('NJE') else 'multiproof-20261107')
  prefix=a.split('_')[0];rp=D/a/'receipt.json';r=json.load(open(rp));assert r['exit_status']==expected,a
  log=read(D/a/'stdout.log');assert 'timed out' not in log.lower(),a
  assert ('VERIFICATION:- SUCCESSFUL' in log or 'VERIFICATION SUCCESSFUL' in log) if expected==0 else ('VERIFICATION:- FAILED' in log or 'VERIFICATION FAILED' in log),a
  V=D/(a+'_validation');g=json.load(open(V/'NHR_GRAPH_CHECK.json'));assert g['graph_matches_frozen'] and not g['added'] and not g['edge_errors']
  assert {tuple(p) for p in g['missing']}<={('aspis-r1-cert-build','0.0.0',None),('aspis-r1-cert-check','0.0.0',None),('aspis-z4b-probe','0.1.0',None)}
  assert not any('r1p-check' in p['features'] for p in g['features'])
  lock=json.load(open(V/(prefix+'_LOCK.json')));assert lock['unchanged'] and lock['before']==lock['after']==g['lock_before']==g['lock_after']
  kmx=V/(prefix+'_KMX.json');inp=json.load(open(V/(prefix+'_INPUTS.json')))
  if prefix in ['NJE','NJP']:assert inp['KMX_patch_sha256']==KMX
  else:assert json.load(open(kmx))['patch_sha256']==KMX
  assert '--locked' not in inp['native_command']
  for p in [rp,D/(a+'.json')]+[p for p in V.rglob('*') if p.is_file()]:pins[str(p)]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
original=json.loads(lzma.decompress((E.parent/'multiproof-20261107/NJA_TARGET_ROWS.json.xz').read_bytes()))
functions=[];packets=[]
for row,root,domain,pairs in [('TX1:306','NJP_PermutationPacket.TX1_306','Canonical M31[16] on original fixed-width public/tree carrier; concrete deployed |_| {} callback; full raw mutable state, returning unit, all 22 event descriptors/values',own_pairs[:2]+inherited),('TX1:305','NJP_CompressionPacket.TX1_305','Both canonical M31[8] digests, SAME 16-limb seed/tweak, full first-eight output, readonly left/right',own_pairs[2:])]:
 original_row=next(r for r in original if r['row']==row)
 f=dict(rows=[row],function=original_row['function'],route='(y)/(ad)/(ai)/(al)/(aq)(5) direct P6 hybrid',root_domain=domain,native_pairs=pairs,lean_roots=[root],complete_carrier=True,premise_policy='Own inputs and reviewed parent stage cuts only; all child models installed at SAME arguments; no arbitrary Ops dictionary or successful-child premise',trust='P6/D188 option A RECLASSIFICATION; existing source/Std/runtime/artifact trust retained; none added/removed')
 functions.append(f)
 clauses=[]
 for c in original_row['obligation']['caller_domain_obligations']:
  copied=dict(c);copied.update(disposition='DISCHARGED',discharged_by=(['NJP_CompressionPacket.child_domain','NJP_CompressionPacket.TX1_305','NJP_K010/NJP_K011/NJP_K012'] if row=='TX1:305' else ['NJE_RoundTrace.facts','NJE_RoundTrace.one','NJE_RoundComposition.cell_law','NJE_ConstantsInitial.canonical','NJE_ConstantsInternal.canonical','NJE_ConstantsFinal.canonical','NJP_PermutationPacket.TX1_306']),type_resolution='Frozen body is scalar M31; conservative CM31/QM31/WideExact alternatives are not reached. Source skeleton and field argument types pinned.');clauses.append(copied)
 packets.append(dict(row=row,function=original_row['function'],root=root,original_inventory=original_row,caller_clauses=clauses,complete_carrier=True,aq2_hypothesis_inventory={'permitted':['own input carrier','reviewed parent cut after SAME-input CLOSED child substitution'],'extra_logical_hypotheses':[],'detail':'TX1:306 Cut expands to controller descriptors plus per-cell/linear witnessed native cuts, not endpoint equality. TX1:305 CallerCut is the arbitrary-reply native caller cut instantiated with the permutation model at its own logged seed. Canonical input clauses belong to compression itself.'},admission='FIRST combined NJK+NJE+deployed/NFX/raw ax2 PASS; local candidate only, next lead ledger gate required'))
closed=dict(frozen_revision=closed_pre['frozen_revision'],headline='AspisR1.RPx_Deployed.deployed',functions=functions,admission='First own combined gate PASS; proposed CLOSED candidates, ledger credit pending',status='CLOSED candidate packets under recorded own domains; not authoritative ledger credit',target_established=False)
audit=dict(target_established=False,combined_audits_used=1,combined_audit_limit=2,headline=closed['headline'],gate1={'combined':'NJP_L025','scan':'NJP_L026','fixtures':'NJP_L024','raw':['NJP_L027'],'modules':len(scan),'raw_roots':len(raw),'coherence_defects':0,'standard_axioms_only':True},ledger_credit_pending=True,cold_release_replay=False)
base=json.loads(lzma.decompress((E.parent/'ledger14-20261108/NJK_LEDGER.json.xz').read_bytes()))
delta=dict(baseline='evidence/ledger14-20261108/NJK_LEDGER.json.xz',baseline_sha256=hashlib.sha256((E.parent/'ledger14-20261108/NJK_LEDGER.json.xz').read_bytes()).hexdigest(),baseline_counts=base['counts'],proposed_rows=['TX1:306','TX1:305'],authoritative_ledger_changed=False,credit_pending=True,required_callee_candidates='NJE 24 packets; next lead ledger gate must admit dependencies and these two packets together',target_established=False)
for name,obj in [('NJP_CLOSED.json',closed),('NJP_ROW_PACKETS.json',packets),('NJP_AUDIT.json',audit),('NJP_LEDGER_DELTA.json',delta),('NJP_REUSED_PINS.json',pins),('NJP_FIXTURES.json',fixtures),('NJP_RAW_RESULTS_GATE1.json',raw)]:
 (E/name).write_text(json.dumps(obj,indent=2)+'\n')
for name in ['NJP_AUDIT_ROOTS.json','NJP_AUDIT_MODULES.json','NJP_EXPECTED_IMPORTS.jsonl','NJP_COMBINED_IMPORT.lean']:(E/('NJP_GATE1_'+name.removeprefix('NJP_'))).write_bytes((E/name).read_bytes())
print('Gate 1 PASS: 2 local candidate rows, '+str(len(scan))+' coherent modules, '+str(len(raw))+' standard-only raw roots; ledger credit pending')
