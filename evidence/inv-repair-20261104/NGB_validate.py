"""Independent read-only validation of the additive repair and honest gap."""
import json,lzma,pathlib,hashlib,collections,copy,subprocess,re
E=pathlib.Path(__file__).resolve().parent;R=E.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
def get(n):return json.loads((E/n).read_text())
def validate(b,l,o,edges,mir):
 old={r['row']:r for r in b['rows']};new={r['row']:r for r in l['rows']};assert len(new)==len(l['rows'])
 assert set(old)<=set(new)
 assert all(new[k]['composed_status']==v['composed_status'] for k,v in old.items())
 assert all(r['composed_status']=='OPEN' for k,r in new.items() if k not in old)
 assert len(o['new_rows'])==len(new)-len(old)
 ix=collections.defaultdict(list)
 for r in l['rows']:ix[r['function']].append(r)
 g=collections.defaultdict(set)
 for r in b['rows']:g[r['function']].update(r['canonical_callees'])
 for e in edges:
  assert e['from'] in ix and e['to'] in ix
  ev=e['evidence'];assert ev['compiler_gate_passed'] is True
  assert ev['method']=='rustc-MIR' and sha((R/ev['path']).read_bytes())==ev['sha256']
  records={m['id']:m for m in json.loads((R/ev['path']).read_text())['edges']}
  for rid in ev['records']:
   m=records[rid];assert m['caller']==e['from'] and m['callee']==e['to'] and m['source_check']=='AGREES' and m['source_sites']
  g[e['from']].add(e['to'])
 for r in l['rows']:assert set(r['canonical_callees'])==g[r['function']]
 assert sha((R/o['edge_list']['path']).read_bytes())==o['edge_list']['sha256']
 return True
base=json.loads(lzma.open(R/'evidence/ledger7-20261104/NFX_LEDGER.json.xz').read());L=json.loads(lzma.open(E/'NGB_ADMITTED_LEDGER.json.xz').read());O=get('NGB_OVERLAY.json');edges=get('NGB_EDGES.json');M=get('NGB_MIR_EDGES.json')
assert sha((R/O['baseline']['path']).read_bytes())==O['baseline']['sha256']
assert validate(base,L,O,edges,M)
# Confirm each compiler pin and every cited MIR line, independently of discovery.
lines={}
for p in M['inputs']:
 b=(R/p['path']).read_bytes();assert sha(b)==p['sha256'];raw=lzma.decompress(b);assert sha(raw)==p['uncompressed_sha256'];lines[p['path']]=raw.decode().splitlines()
for m in M['edges']+get('NGB_TRANSITIVE_MIR_EDGES.json')['edges']:
 assert lines[m['mir_path']][m['mir_line']-1].strip()==m['mir_text']
 assert m['source_check']=='AGREES' and m['source_sites']
assert len([m for m in M['edges'] if '::Transcript<H>::queries' in (m['caller'] or '') and m['callee'].endswith('WideExact::from_m31')])==22
resolved=get('NGB_CANDIDATES_RESOLVED.json');assert len(resolved['candidates'])==39
assert {r['candidate'] for r in resolved['candidates']}=={f'NFZ_C{i:04}' for i in range(1,40)}
assert [r['candidate'] for r in resolved['candidates'] if r['disposition']=='UNRESOLVED-EVIDENCE']==['NFZ_C0032']
assert not (R/'evidence/inv-defects-20261104/NFZ_aspis_statement.mir').read_bytes()
assert all('extension_limbs' not in s for ls in lines.values() for s in ls)
coverage=get('NGB_COVERAGE.json');assert len(coverage['rows'])==len(L['rows'])
assert all(c['slices'] for c in coverage['rows'])
assert all(len(p.read_bytes())<=20*1024*1024 for p in E.iterdir() if p.is_file())
for p in get('NGB_Q_SOURCE_PINS.json'):
 raw=(R/p['path']).read_bytes() if (R/p['path']).exists() else subprocess.check_output(['git','show','HEAD:'+p['path']],cwd=R)
 assert sha(raw)==p['sha256']
# Matched corruption controls for our own additive validator (not native credit).
controls={}
for name in ['status_promotion','missing_edge','unproved_new_row','bad_evidence_pin']:
 b=copy.deepcopy(base);l=copy.deepcopy(L);o=copy.deepcopy(O);ee=copy.deepcopy(edges)
 if name=='status_promotion':l['rows'][0]['composed_status']='OPEN'
 if name=='missing_edge':l['rows'][next(i for i,r in enumerate(l['rows']) if r['function']==ee[0]['from'])]['canonical_callees'].remove(ee[0]['to'])
 if name=='unproved_new_row':l['rows'][-1]['composed_status']='CLOSED'
 if name=='bad_evidence_pin':ee[0]['evidence']['sha256']='0'*64
 try:validate(b,l,o,ee,M)
 except AssertionError:controls[name]='REJECTED'
 else:raise AssertionError('accepted corruption '+name)
print(json.dumps(dict(result='PASS_WITH_EXPLICIT_C0032_GAP',rows=len(L['rows']),admitted_edges=len(edges),new_rows=len(O['new_rows']),coverage=len(coverage['rows']),candidate_dispositions=resolved['dispositions'],corruption_controls=controls,compiler_scopes=0,axioms='N/A; no new theorem')))
