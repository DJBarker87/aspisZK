#!/usr/bin/env python3
"""Additive NEZ receipt-ledger extension. Status checks only, no prover runs.

NEZ's exact output, tests, denial history and certificate semantics are retained.
Successful immutable slice replays are reused, not rerun or replaced by headlines.
New gates bind the checked occurrence to its full certificate and receipt corpus,
then impose ax2, trust inventory and headline-coherence requirements.
"""
import argparse
import ast
import collections
import copy
import hashlib
import json
import lzma
from pathlib import Path
import re
import subprocess
import sys
sys.dont_write_bytecode = True
E = Path(__file__).resolve().parent
R = E.parent.parent
REV = '9905ea55a106eadbf120088a8b7601c6fa7c2843'
NFJ_REV = 'eeaa04cfaf3'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
NEV_ROWS = {'TX1:185', 'TX2:111', 'TX1:182', 'TX2:108'}
QUALIFIED = {'TX1:181', 'TX2:104'}
LANES = dict(NEW='slice-q-compose4-20261104', NFB='slice-q-compose5-20261104',
 NFA='slice-q-mul4-20261104', NFC='slice-q-mul5-20261104',
 NFE='slice-q-mul6-20261104', NFF='slice-q-mul7-20261104',
 NEY='slice-s-compose9-20261104', NFD='slice-s-compose10-20261104',
 NFH='slice-s-compose11-20261104', NFJ='slice-s-compose12-20261104')
TRUST = {
 'RuntimeReturnData': dict(id='RuntimeReturnData', ruling='ab', classification='ADDED trust; owner confirmation pending', scope='Same instruction context and program, immediate exact return-data readback; Pool association remains separately OPEN'),
 'RuntimeMemcmp': dict(id='RuntimeMemcmp', ruling='ac', classification='ADDED trust; owner confirmation pending', scope='SAME two valid readable 688-byte ranges; supplied i32 output slot zero iff equal; normal return, no input/state/event change; no ordering/sign/timing assumption')}

def require(ok, message):
 if not ok: raise ValueError(message)

def sha(raw): return hashlib.sha256(raw).hexdigest()
def encode(value): return json.dumps(value, indent=1, sort_keys=True)+'\n'
def walk(value):
 yield value
 if isinstance(value, dict):
  for v in value.values(): yield from walk(v)
 elif isinstance(value, list):
  for v in value: yield from walk(v)

class Corpus:
 """Read committed inputs only; record every consumed blob, including sparse ones."""
 def __init__(self): self.pins = {}; self.cache = {}
 def raw(self, path):
  path = str(path)
  revision = NFJ_REV if path.startswith('evidence/'+LANES['NFJ']+'/') else REV
  key = revision+':'+path
  if key not in self.cache:
   p = subprocess.run(['git','show',key],cwd=R,capture_output=True)
   if p.returncode: raise FileNotFoundError(key)
   raw = p.stdout
   local = R/path
   # HEAD deliberately lacks NFJ; never substitute a later worker's live files.
   if revision == REV and local.is_file(): require(local.read_bytes()==raw,'dirty input: '+path)
   self.cache[key] = raw
   self.pins[path] = dict(revision=revision,sha256=sha(raw),bytes=len(raw))
  return self.cache[key]
 def obj(self, path):
  try: raw=self.raw(path)
  except FileNotFoundError:
   raw=lzma.decompress(self.raw(path+'.xz'))
   require(sha(raw)==self.raw(path+'.sha256').decode().strip(),'transport digest: '+path)
  return json.loads(raw)
 def lane(self, prefix, name): return self.obj('evidence/'+LANES[prefix]+'/'+name)
 def support(self, value):
  for item in walk(value):
   if isinstance(item,dict) and {'path','sha256'} <= item.keys() and str(item['path']).startswith(('evidence/','docs/')):
    require(sha(self.raw(item['path']))==item['sha256'],'support pin: '+item['path'])


def standard_prints(lines):
 require(bool(lines),'missing axioms output')
 for line in lines:
  m=re.search(r'axioms: \[([^]]*)\]',line)
  require('does not depend on any axioms' in line or (m and {x.strip() for x in m[1].split(',') if x.strip()} <= STANDARD),'nonstandard or missing axioms: '+line)

def fixtures(rows):
 expected={'NEP_Planted.matcher':['NEP_Planted.matchAx'], 'NEP_Planted.viaPrivate':['NEP_Planted.privateAx'],
 'NEP_Planted.proof':['NEP_Planted.proofAx'], 'NEP_Planted.viaAux':['NEP_Planted.auxAx'],
 'NEP_MutateMatch.matcher':[], 'NEP_MutatePrivate.viaPrivate':[], 'NEP_MutateProof.proof':[], 'NEP_MutateAux.viaAux':[]}
 require(len(rows)==8,'ax2 fixture count')
 require({r['root']:r['walked_axioms'] for r in rows}==expected,'ax2 fixture outcomes')
 require(all(r['equal'] and r['collect_axioms']==r['walked_axioms'] for r in rows),'ax2 collectAxioms mismatch')

def nev_audit(c):
 """A failed/missing replay denies all four NEV occurrences, even inherited ones."""
 try:
  a=c.lane('NFC','NFC_AUDIT.json'); n=c.lane('NFA','NFA_AUDIT.json')
  require(a['status']=='PASS_AX2_CONDITION_3' and a['walker_unchanged'],'NFC ax2 status')
  require(n['walker_unchanged'] and n['standard_axioms_only'] and n['zero_unresolved_constants'],'NFA raw audit')
  require(n['unique_roots']==152 and set(a['rows_credited'])==NEV_ROWS,'NEV audit subject')
  fixtures(a['fixtures'])
  require(len(n['results'])==152 and all(r['equal'] and r['collect_axioms']==r['walked_axioms'] and set(r['walked_axioms'])<=STANDARD for r in n['results']),'NFA raw reachable-axiom sets')
  require(a['walker_sha256']==sha(c.raw('evidence/'+LANES['NFA']+'/NFA_WALKER.lean')),'ax2 walker identity')
  require(sha(c.raw('evidence/'+LANES['NFC']+'/NFC_DRIVER.diff'))==a['driver_diff_sha256'],'ax2 driver diff')
  for entry in n['attempts']:
   require(entry['exit_status']==0 and int(entry['swaps'])==0,'NFA audit receipt status')
   standard_prints(entry['print_axioms'])
  r=c.lane('NFC','NFC_L005/receipt.json')
  require(r['exit_status']==0 and int(r['swaps'])==0 and r['module']=='fixtures','missing NFC fixture replay')
  log=c.raw('evidence/'+LANES['NFC']+'/NFC_L005/stdout.log').decode()
  require(all(row['root'] in log for row in a['fixtures']),'fixture replay output absent')
  return True, 'NFC_L005 fixtures and NFA 152-root standard-only raw audit reused'
 except (FileNotFoundError,KeyError,ValueError) as error: return False, str(error)


def root_certificates(packet, function):
 return [v for v in walk(packet) if isinstance(v,dict) and v.get('subject')==function and 'semantic_review_sha256' in v]

def certificate_checks(c, certificate):
 require(bool(certificate),'Missing complete row/call-domain/hypothesis composition certificate')
 c.support(certificate)
 for item in walk(certificate):
  if isinstance(item,dict) and 'semantic_review_sha256' in item:
   require(item['semantic_review_sha256']==sha(json.dumps({k:v for k,v in item.items() if k!='semantic_review_sha256'},sort_keys=True).encode()),'semantic certificate review digest')
  if isinstance(item,dict) and 'inner_hypotheses_remaining' in item: require(item['inner_hypotheses_remaining']==[],'residual inner hypotheses')
  if isinstance(item,dict) and 'remaining_inner_hypotheses' in item: require(item['remaining_inner_hypotheses']==[],'residual inner hypotheses')


def row_checks(row, base, certificate):
 reasons=[]
 if not certificate: reasons.append('Missing complete row/call-domain/hypothesis composition certificate')
 if (row['row'],row['function'],row['frozen_body_sha256']) != (base['row'],base['function'],base['frozen_body_sha256']): reasons.append('candidate frozen identity mismatch')
 if row['bridge_status']!='CLOSED-CONDITIONAL' or not row['selected_claims']: reasons.append('Missing conditional bridge or selected claim')
 if row['open_transitive_dependencies']: reasons.append('Open transitive dependencies')
 if any(not h['discharged_by'] for h in row['named_hypotheses']): reasons.append('Undischarged named hypothesis')
 if any(o['status']!='CLOSED' or not o['discharged_by'] for o in row['caller_domain_obligations']): reasons.append('Open caller-domain obligation')
 # Preserve NEZ active receipt denials; an old suspended receipt is never restored.
 denied={x['receipt'] for x in BASE_CREDITS if x.get('k2_quarantined') or x.get('k3_status')=='SUSPENDED'}
 if denied & set(row.get('active_support_receipts',[])): reasons.append('NEZ K-2/K-3 active support denial')
 return reasons
BASE_CREDITS=[]


def trust_tags(row, certificate):
 tags=set(row.get('NEZ_trust_rows',[]))
 # Inspect selected semantic certificate, never unrelated history or audit roots.
 text=encode(certificate)
 if re.search(r'RuntimeReturnData|NEX_EmitRuntime|NFD_EmitRuntime|set_return_data',text): tags.add('RuntimeReturnData')
 if re.search(r'RuntimeMemcmp|NFH_ComparisonDomain.At688Law',text): tags.add('RuntimeMemcmp')
 return sorted(tags & TRUST.keys())


def admit(base, candidates, certificates, reported, audit_ok=True, audit_reason=''):
 """Only additive checked candidates; QUALIFIED is distinct from CLOSED."""
 out=copy.deepcopy(base); by={r['row']:r for r in out['rows']}; original={r['row']:r for r in base['rows']}
 for rid,(provider,candidate) in candidates.items():
  row=copy.deepcopy(candidate); cert=certificates.get(rid)
  reasons=row_checks(row,original[rid],cert)
  row['NFK_provider']=provider; row['NFK_rejections']=reasons
  row['NFK_trust_rows']=trust_tags(row,cert)
  if reasons: row['composed_status']='OPEN'; row['bridge_status']='OPEN'
  elif rid in QUALIFIED:
   row['composed_status']='QUALIFIED'
   row['NFK_rejections']=['Source-validator CLOSED; headline import duplicates verifier.Phase (NFF_FINDINGS.md L032); coherent retarget replay not in this pinned refresh']
  by[rid].update(row)
 for row in out['rows']:
  rid=row['row']; row.setdefault('NFK_rejections',[])
  row.setdefault('NFK_trust_rows',trust_tags(row,{}))
  if rid in NEV_ROWS and not audit_ok:
   row['composed_status']='OPEN'; row['bridge_status']='OPEN';row['NFK_rejections']=['NEV ax2 replay unavailable or nonstandard: '+audit_reason]
  row['NFK_reported_closed_by']=[p for p,ids in reported.items() if rid in ids]
 # Exact selected callee claims only; conservative unselected alternatives do not propagate.
 changed=True
 while changed:
  changed=False
  denied={claim for r in out['rows'] if r['composed_status']!='CLOSED' for claim in r['selected_claims']}
  accepted={claim for r in out['rows'] if r['composed_status']=='CLOSED' for claim in r['selected_claims']}
  for row in out['rows']:
   if row['composed_status']!='CLOSED':continue
   if any((set(o.get('callee_claims',[])) & denied)-accepted for o in row['caller_domain_obligations']):
    row['composed_status']='OPEN';row['NFK_rejections']=['Selected active callee claim denied or QUALIFIED'];changed=True
 # Propagate added trust through selected callee claims, without inventing dependencies.
 changed=True
 while changed:
  changed=False; claims={}
  for row in out['rows']:
   if row['composed_status']=='CLOSED':
    for claim in row['selected_claims']:claims.setdefault(claim,set()).update(row['NFK_trust_rows'])
  for row in out['rows']:
   tags=set(row['NFK_trust_rows'])
   for ob in row['caller_domain_obligations']:
    for claim in ob.get('callee_claims',[]):tags.update(claims.get(claim,()))
   if tags!=set(row['NFK_trust_rows']):row['NFK_trust_rows']=sorted(tags);changed=True
 out['NFK_rejected_slice_closures']=[dict(row=r['row'],function=r['function'],status=r['composed_status'],reported_by=r['NFK_reported_closed_by'],reasons=r['NFK_rejections']) for r in out['rows'] if r['NFK_reported_closed_by'] and r['composed_status']!='CLOSED']
 return out


def materialize_recipe(base, cert, provider, edges):
 row=copy.deepcopy(base)
 require(cert['row']==row['row'] and cert['function']==row['function'],'recipe identity')
 if 'frozen_body_sha256' in cert: require(cert['frozen_body_sha256']==row['frozen_body_sha256'],'recipe body')
 row.update(bridge_status='CLOSED-CONDITIONAL',composed_status='CLOSED',selected_claims=[provider+'::'+row['function']],open_transitive_dependencies=[])
 row['named_hypotheses']=[dict(name=provider+'::'+row['function']+'.'+k,statement=cert['domain']+'; '+', '.join(cert.get('top_hypotheses',[])),discharged_by=cert['id']) for k in ['PacketDomain','PhysicalInterpretation']]
 for ob in row['caller_domain_obligations']:
  if 'callee' in ob:
   edge=next((e for e in edges['edges'] if e['edge']==row['function']+' -> '+ob['callee']),None)
   require(edge and edge['status']=='CLOSED' and edge.get('certificate'),'missing Q call-domain certificate: '+ob['id'])
  else:require(ob['id'] in cert['external_obligations'],'missing Q external certificate: '+ob['id'])
  ob.update(status='CLOSED',discharged_by=cert['id']+'::'+ob['id'])
 row['active_support_receipts']=[] # exact selected source/native recipe is in NFK_certificates
 return row


def build():
 global BASE_CREDITS
 c=Corpus(); base=c.obj('evidence/ledger5-20261104/NEZ_LEDGER.json')
 require(len(base['rows'])==587 and sum(r['composed_status']=='CLOSED' for r in base['rows'])==202,'NEZ authoritative baseline')
 BASE_CREDITS=base['NEZ_credits']
 for name in ['NEZ_FINAL.json','NEZ_TESTS.json','NEZ_ARTIFACTS_CANONICAL.json']:
  receipt=c.obj('evidence/ledger5-20261104/'+name);require(receipt['exit_status']==0,'NEZ reused receipt')
  for path,digest in receipt['source_sha256'].items():
   current=c.raw(path)
   if sha(current)!=digest:
    require(path.endswith('/NEZ_validate.py'),'NEZ replay source pin: '+path)
    historical=subprocess.check_output(['git','show',receipt['source_revision']+':'+path],cwd=R)
    require(sha(historical)==digest,'NEZ historical validator pin')
    def semantic(raw):
     tree=ast.parse(raw);tree.body=[n for n in tree.body if not(isinstance(n,ast.FunctionDef) and n.name=='markdown')]
     return ast.dump(tree,include_attributes=False)
    require(semantic(current)==semantic(historical),'NEZ non-reporting source drift')
    c.pins[path+'@'+receipt['source_revision']]=dict(revision=receipt['source_revision'],path=path,sha256=digest,bytes=len(historical))
 c.raw('evidence/ledger5-20261104/NEZ_tests.py')
 spec=c.obj('docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json')['slices']
 c.raw('docs/research/100bit-spend-path-20261013/design/C3-BIN-20261021.md')
 candidates={}; certs={}; by={r['row']:r for r in base['rows']}
 reported=copy.deepcopy(base['NEZ_slice_validator_results']);reported['NEZ']=[r['row'] for r in base['rows'] if r['composed_status']=='CLOSED']
 # Source-checker implementations and full replay receipts are immutable reused inputs.
 for prefix,directory in LANES.items():
  c.raw('evidence/'+directory+'/'+prefix+'_HANDOFF.md')
  try:c.raw('evidence/'+directory+'/'+prefix+'_validate.py')
  except FileNotFoundError: require(prefix in {'NFA','NFC'},'missing slice validator')
  c.lane(prefix,prefix+'_LEDGER_DELTA.json')
 new=c.lane('NEW','NEW_CERTIFICATES.json'); geometry=c.lane('NFB','NFB_CERTIFICATES.json')
 # Exact successful root checks from their immutable source-validator final receipts.
 final=c.lane('NEW','NEW_FINAL_REVIEW.json');require(final['validator_exit_status']==0 and final['tests_exit_status']==0,'NEW final check')
 nfb_log=c.raw('evidence/'+LANES['NFB']+'/NFB_FULL_VALIDATION.stdout').decode()
 require(json.loads(nfb_log)==c.lane('NFB','NFB_LEDGER_DELTA.json'),'NFB replay output drift')
 for prefix,recipes in [('NEW',new),('NFB',geometry)]:
  reported[prefix]=sorted(set(reported['NET']) | {x['row'] for x in new} | ({x['row'] for x in geometry} if prefix=='NFB' else set()))
  for cert in recipes:
   certificate_checks(c,cert)
   rid=cert['row']
   row=cert.get('original_composed_row') or materialize_recipe(by[rid],cert,prefix,c.lane(prefix,prefix+'_EDGES.json'))
   if rid not in NEV_ROWS: candidates[rid]=(prefix,row);certs[rid]=cert
 # NEW/NEV peer source/native certificate rows are reused under the newly admitted audit.
 nev=c.obj('evidence/slice-q-mul3-20261103/NEV_DERIVED_LEDGER.json')
 union=c.obj('evidence/slice-q-mul3-20261103/NEV_UNION_CERTIFICATES.json')
 audit_ok,audit_reason=nev_audit(c)
 for row in nev['rows']:
  if row['row'] not in NEV_ROWS:continue
  rid=row['row'];cert=union['rows'].get(rid) or base['NEZ_certificates'][rid]
  certificate_checks(c,cert);require(row['composed_status']=='CLOSED','NEV checked occurrence not closed')
  candidates[rid]=('NFC',row);certs[rid]=cert
 reported['NFA']=[];reported['NFC']=sorted(NEV_ROWS)
 for prefix in ['NFA','NFC','NFE','NFF']:c.lane(prefix,prefix+'_CLOSED.json')
 for prefix in ['NFE','NFF']:
  delta=c.lane(prefix,prefix+'_LEDGER_DELTA.json')
  require(delta['new_count']==0 and not delta['newly_closed'],'unsupported arithmetic closure')
  reported[prefix]=sorted(set(reported['NET']) | {x['row'] for x in new})
 # NFJ's checked output is the immutable final cumulative S replay, not a headline count.
 srows=c.lane('NFJ','NFJ_CHECKED_ROWS.json');summary=c.lane('NFJ','NFJ_VALIDATION.json')
 require(len(srows)==97 and all(r['composed_status']=='CLOSED' for r in srows),'NFJ checked row corpus')
 require(summary['closed_rows']==97 and summary['closed_edges']==129 and summary['closed_roots']==7,'NFJ final status')
 audit=c.lane('NFJ','NFJ_AUDIT.json');receipt=c.lane('NFJ','NFJ_L012/receipt.json')
 require(audit['status']=='PASS' and audit['root_count']==88 and audit['zero_unresolved'] and audit['walker_byte_identical'],'NFJ ax2 status')
 require(receipt['exit_status']==0 and int(receipt['swaps'])==0,'NFJ raw audit receipt')
 require(receipt['command']==['NFJ_native/NFJ_Driver','final'],'NFJ raw walker executable');standard_prints(audit['print_axioms'])
 fx=c.lane('NFJ','NFJ_FIXTURES.json');fixtures(fx['fixtures'])
 require(fx['driver_binary_sha256']==audit['driver_binary_sha256'],'NFJ same fixture/final driver')
 fr=c.lane('NFJ','NFJ_L011/receipt.json');require(fr['exit_status']==0 and int(fr['swaps'])==0,'NFJ fixture receipt')
 require(len(audit['results'])==88 and all(r['equal'] and set(r['walked_axioms'])<=STANDARD and r['collect_axioms']==r['walked_axioms'] for r in audit['results']),'NFJ raw audit roots')
 packets={p:c.lane(p,p+'_LEDGER_DELTA.json') for p in ['NEY','NFD','NFJ']}
 sproviders={}
 for row in srows:
  rid=row['row']; provider=None;selected=None
  for prefix,packet in packets.items():
   found=root_certificates(packet,row['function'])
   if found: provider=prefix;selected=found
  sproviders[rid]=provider
  if by[rid]['composed_status']=='CLOSED':continue # all inherited NEZ denial/history remains exact
  require(selected is not None,'new S row missing complete selected recipe: '+rid)
  certificate_checks(c,selected)
  candidates[rid]=(provider,row);certs[rid]=selected
 for prefix,count in [('NEY',86),('NFD',96),('NFH',96),('NFJ',97)]:
  # Exact earlier S closed list is reconstructible from checked rows and new providers.
  reported[prefix]=sorted(r['row'] for r in srows if not (prefix=='NEY' and sproviders[r['row']] in {'NFD','NFJ'}) and not(prefix in {'NFD','NFH'} and sproviders[r['row']]=='NFJ'))
  require(len(reported[prefix])==count,'S stage occurrence reconciliation: '+prefix)
 out=admit(base,candidates,certs,reported,audit_ok,audit_reason)
 out['NFK_certificates']=certs
 out['NFK_source_revision']=REV;out['NFK_NFJ_source_revision']=NFJ_REV
 out['NFK_validation_mode']='Immutable successful receipt reuse plus additive Python status/certificate checks; no slice validator, Lean or Kani rerun'
 out['NFK_nev_audit']=dict(admitted=audit_ok,reason=audit_reason,rows=sorted(NEV_ROWS))
 out['NFK_budget']=dict(lean_runs=0,kani_runs=0,native_builds=0)
 out['NFK_slice_validator_results']=reported
 out['NFK_lane_dispositions']={p:dict(directory=directory,delta=c.lane(p,p+'_LEDGER_DELTA.json'),validation='successful immutable replay reused; additive NFK checks only',reported_closed_count=len(reported[p])) for p,directory in LANES.items()}
 out['NFK_historical_fields']='NDT/NEN/NEZ fields retain historical evidence; NFK fields and row composed_status govern this checkpoint'
 out['trust_rows']=copy.deepcopy(base['trust_rows'])
 for name,addition in TRUST.items():
  existing=next((t for t in out['trust_rows'] if t['id']==name),None)
  if existing is None:out['trust_rows'].append(copy.deepcopy(addition))
  else:
   existing['NFK_classification']=addition['classification'];existing['NFK_ruling']=addition['ruling']
 summarize(out,spec)
 out['NFK_inputs']=dict(sorted(c.pins.items()))
 return out


def summarize(out,spec):
 rows=out['rows']
 def counts(rs):
  statuses=collections.Counter(r['composed_status'] for r in rs)
  return dict(total=len(rs),CLOSED=statuses['CLOSED'],QUALIFIED=statuses['QUALIFIED'],OPEN=statuses['OPEN'])
 out['NFK_coverage']={k:counts([r for r in rows if k=='all_rows' or r['row'].startswith(k+':')]) for k in ['all_rows','TX1','TX2']}
 out['NFK_per_function']={f:dict(**counts([r for r in rows if r['function']==f]),rows=[r['row'] for r in rows if r['function']==f]) for f in sorted({r['function'] for r in rows})}
 out['NFK_unique_functions']=dict(total=len(out['NFK_per_function']),fully_CLOSED=sum(v['CLOSED']==v['total'] for v in out['NFK_per_function'].values()),with_CLOSED_occurrence=sum(v['CLOSED']>0 for v in out['NFK_per_function'].values()),with_QUALIFIED_occurrence=sum(v['QUALIFIED']>0 for v in out['NFK_per_function'].values()))
 out['NFK_slices']={}
 for lane in ['Q','S']:
  selected=[r for r in rows if r['function'] in spec[lane]['functions']]
  roots=[dict(function=f,rows=[r['row'] for r in rows if r['function']==f],status='CLOSED' if all(r['composed_status']=='CLOSED' for r in rows if r['function']==f) else ('QUALIFIED' if any(r['composed_status']=='QUALIFIED' for r in rows if r['function']==f) else 'OPEN')) for f in spec[lane]['roots']]
  out['NFK_slices'][lane]=dict(**counts(selected),per_tx={tx:counts([r for r in selected if r['row'].startswith(tx+':')]) for tx in ['TX1','TX2']},unique_functions=sum(all(r['composed_status']=='CLOSED' for r in selected if r['function']==f) for f in {r['function'] for r in selected}),roots=roots,roots_CLOSED=sum(r['status']=='CLOSED' for r in roots))
 out['NFK_qualified_rows']=[r['row'] for r in rows if r['composed_status']=='QUALIFIED']
 out['NFK_trust_usage']={trust:dict(classification=TRUST[trust]['classification'],**counts([r for r in rows if trust in r['NFK_trust_rows']]),rows=[r['row'] for r in rows if trust in r['NFK_trust_rows']],closed_rows=[r['row'] for r in rows if trust in r['NFK_trust_rows'] and r['composed_status']=='CLOSED']) for trust in TRUST}
 # Current coverage replaces only this derived summary; historical NEZ coverage is preserved explicitly.
 out['NFK_prior_coverage']=out['coverage'];out['coverage']=out['NFK_coverage']


def markdown(d):
 lines=['# NFK authoritative ledger','','Target not yet established. Conditional source composition; no cold release or whole headline replay.','',
 'The exact NEZ 202/587 checkpoint is retained and extended using immutable successful receipts. NFJ inputs come from merged commit `eeaa04cfaf3`: HEAD `'+REV+'` removed that evidence directory. This refresh records the historical merge explicitly. No Lean, Kani or native build ran.','',
 '| Scope | Total | CLOSED | QUALIFIED | OPEN |','|---|---:|---:|---:|---:|']
 for key in ['all_rows','TX1','TX2']:
  val=d['NFK_coverage'][key];lines.append(f"| {key} | {val['total']} | {val['CLOSED']} | {val['QUALIFIED']} | {val['OPEN']} |")
 for key,val in d['NFK_slices'].items():
  lines.append(f"| slice {key} (overlapping membership) | {val['total']} | {val['CLOSED']} | {val['QUALIFIED']} | {val['OPEN']} |")
  for tx,v in val['per_tx'].items():lines.append(f"| {key} {tx} | {v['total']} | {v['CLOSED']} | {v['QUALIFIED']} | {v['OPEN']} |")
 lines+=['','Unique functions: '+json.dumps(d['NFK_unique_functions'],sort_keys=True)+'. Slice overlap is counted once globally. Per-function counts and rows follow below.','','## Roots','']
 for lane,s in d['NFK_slices'].items():
  lines.append(f"Slice {lane}: {s['roots_CLOSED']}/{len(s['roots'])} roots CLOSED; {s['unique_functions']} fully CLOSED unique functions.")
  for r in s['roots']:lines.append('- `'+r['function']+'`: '+r['status']+' ('+', '.join(r['rows'])+').')
 lines+=['','## Added runtime trust (owner confirmation pending)','']
 for trust in sorted(d['NFK_trust_usage']):
  v=d['NFK_trust_usage'][trust];lines.append(f"- {trust}: {v['CLOSED']} CLOSED, {v['QUALIFIED']} QUALIFIED, {v['OPEN']} OPEN occurrences. Rows: {', '.join(v['rows'])}. {v['classification']}.")
 lines+=['','These runtime rows are additions, not discharged cryptographic or native implementation obligations. Rejecting (ab) reopens emit_result; rejecting (ac) reopens scan_proof_buffer. Pool return-data association remains separately OPEN.','','## Rejected slice-reported CLOSED rows','']
 for r in d['NFK_rejected_slice_closures']:lines.append('- '+r['row']+' `'+r['function']+'`: '+r['status']+'; reported by '+', '.join(r['reported_by'])+'; '+'; '.join(r['reasons']))
 lines+=['','NFA withholds admission; NFC admits exactly the four inherited NEV rows after ax2. NEW/NFB and NFE/NFF cumulative reports overlap these rows; their totals are never added together. Historical NEZ slice rejections remain included.','','## Exact function coverage','','| Function | Occurrences | CLOSED | QUALIFIED | OPEN |','|---|---:|---:|---:|---:|']
 for f,v in d['NFK_per_function'].items():lines.append(f"| {f} | {v['total']} | {v['CLOSED']} | {v['QUALIFIED']} | {v['OPEN']} |")
 lines+=['','## Every occurrence','','| Row | Function | Status | Added trust | Reason |','|---|---|---|---|---|']
 for r in d['rows']:lines.append(f"| {r['row']} | {r['function']} | {r['composed_status']} | {', '.join(r['NFK_trust_rows'])} | {'; '.join(r['NFK_rejections'])} |")
 return '\n'.join(lines)+'\n'


def main():
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--write',action='store_true');args=parser.parse_args()
 d=build()
 for name,raw in [('NFK_LEDGER.json',encode(d).encode()),('NFK_LEDGER.md',markdown(d).encode())]:
  path=E/name
  if len(raw)>20_000_000:
   compressed=Path(str(path)+'.xz');digest=Path(str(path)+'.sha256')
   if args.write:compressed.write_bytes(lzma.compress(raw,preset=6));digest.write_text(sha(raw)+'\n')
   else:require(lzma.decompress(compressed.read_bytes())==raw and digest.read_text().strip()==sha(raw),'output drift: '+name)
  elif args.write:path.write_bytes(raw)
  else:require(path.read_bytes()==raw,'output drift: '+name)
 print(encode(dict(coverage=d['NFK_coverage'],unique_functions=d['NFK_unique_functions'],slices=d['NFK_slices'],trust=d['NFK_trust_usage'],rejected=d['NFK_rejected_slice_closures'],input_blobs=len(d['NFK_inputs']))))
if __name__=='__main__':main()
