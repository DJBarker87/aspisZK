#!/usr/bin/env python3
"""Add certificate gates to NDT; never modify its existing acceptance checks.

A syntactically valid certificate is not a theorem prover. Semantic theorem/
callsite review is pinned by NED_REVIEWED_CERTIFICATES.json. Model-only work
is deliberately ineligible for native composition credit.
"""
from pathlib import Path
import argparse,copy,hashlib,importlib.util,json,re,sys
E=Path(__file__).resolve().parent;R=E.parent.parent
sys.path.insert(0,str(R/'evidence/native-ledger3-20261029'))
import NDT_validate as ndt
sha=lambda b:hashlib.sha256(b).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def artifact(ref):
 p=R/ref['path'];assert p.is_file(),('missing artifact',str(p))
 b=p.read_bytes();assert sha(b)==ref['sha256'],('artifact hash',str(p));return b

def theorem(t):
 source=artifact(t['source']).decode();receipt=json.loads(artifact(t['receipt']))
 assert receipt['kind']=='lean' and receipt['exit_status']==0
 assert float(receipt['wall_seconds'])>=0 and int(receipt['peak_rss_kib'])>0
 assert int(receipt['swaps'])==0 and receipt['source_revision']
 assert receipt['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert receipt['source_hashes'].get(t['snapshot_path'])==t['source']['sha256']
 assert '#print axioms '+t['name'].split('.')[-1] in source or '#print axioms '+t['name'] in source
 audits=[x for x in receipt['print_axioms'] if x.startswith("'"+t['name']+"'")]
 assert len(audits)==1,('missing axioms',t['name'])
 names=re.search(r'\[([^]]*)\]',audits[0])
 assert names or 'does not depend on any axioms' in audits[0]
 if names:assert set(x.strip() for x in names[1].split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'}
 assert not re.search(r'\b(sorry|admit|native_decide)\b',source)
 assert t['statement'] in source and sha(t['statement'].encode())==t['statement_sha256']
 return True

def certificate(c,expected,ledger,reviewed):
 try:
  assert c and c['kind'] in {'call-domain','root-composition','alternative-resolution','hypothesis-discharge'}
  assert c['subject']==expected and c['frozen_revision']==ledger['frozen_revision']
  assert c['semantic_review_sha256']==reviewed.get(expected)==sha(json.dumps({k:v for k,v in c.items() if k!='semantic_review_sha256'},sort_keys=True).encode())
  assert c['theorems'] and all(theorem(t) for t in c['theorems'])
  assert c['native_association'] and c['same_inputs'] and c['same_carrier'] and c['same_state'] and c['same_result'] and c['ordered_effects']
  for ref in c['native_association']:artifact(ref)
  assert c['inner_hypotheses_remaining']==[]
  assert c['physical_interpretation_derivation']
  if c['kind']=='root-composition':
   allowed={expected+'.PacketDomain',expected+'.PhysicalInterpretation','RuntimePersistence','CompositionTrustOptionA'}|{t['id'] for t in ledger['trust_rows']}
   assert set(c['hypotheses'])<=allowed
  else:assert c['callee_domain_established'] and c['canonical_carrier_established']
  return True
 except (AssertionError,KeyError,ValueError,TypeError,OSError):return False

def compose(base,packet,reviewed):
 ndt.validate_invariants(base) # ALL original NDT invariants, unchanged.
 assert sha((R/'evidence/native-ledger3-20261029/NDT_LEDGER.json').read_bytes())==packet['base_sha256']
 assert packet['frozen_revision']==base['frozen_revision']
 spec=read(R/'docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json')['slices']['S']
 assert set(packet['edges'])<=set(spec['internal_edges'])
 assert set(packet['roots'])<=set(spec['roots'])
 out=copy.deepcopy(base);byfunction={}
 for row in out['rows']:byfunction.setdefault(row['function'],[]).append(row)
 # Discharge only explicit named hypotheses, with separate same-call certificates.
 for row in out['rows']:
  if row['function'] not in spec['functions']:continue
  for ob in row['caller_domain_obligations']:
   edge=ob.get('caller',row['function'])+' -> '+ob.get('callee','<unresolved>');c=packet['edges'].get(edge)
   if certificate(c,edge,base,reviewed):ob.update(status='CLOSED',discharged_by=c['id'])
  for h in row['named_hypotheses']:
   key=row['function']+'::'+h['name'];c=packet['hypotheses'].get(key)
   if certificate(c,key,base,reviewed):h['discharged_by']=c['id']
 # Bottom-up fixed point; unresolved cycles and alternative targets remain OPEN.
 changed=True
 while changed:
  changed=False
  for f in spec['functions']:
   rs=byfunction[f];c=packet['roots'].get(f) or packet['members'].get(f)
   if not certificate(c,f,base,reviewed):continue
   for row in rs:
    if row['composed_status']=='CLOSED':continue
    deps=[g for g in row['canonical_callees'] if not certificate(packet['edges'].get(f+' -> '+g),f+' -> '+g,base,reviewed) or packet['edges'][f+' -> '+g]['kind']!='alternative-resolution']
    if row['bridge_status']!='CLOSED-CONDITIONAL' or not row['selected_claims']:continue
    if any(not h['discharged_by'] for h in row['named_hypotheses']):continue
    if any(o['status']!='CLOSED' or not o['discharged_by'] for o in row['caller_domain_obligations']):continue
    if any(any(r['composed_status']!='CLOSED' for r in byfunction[g]) for g in deps):continue
    if row['open_transitive_dependencies']:continue # baseline OPEN bridges cannot be erased by composition
    row.update(composed_status='CLOSED',composed_reason='NED reviewed same-call certificates '+c['id']);changed=True
 ndt.validate_invariants(out) # original postconditions must still hold.
 return out

def main():
 p=argparse.ArgumentParser();p.add_argument('--packet',type=Path,default=E/'NED_LEDGER_DELTA.json');p.add_argument('--write',type=Path);a=p.parse_args()
 base=read(R/'evidence/native-ledger3-20261029/NDT_LEDGER.json');packet=read(a.packet);reviewed=read(E/'NED_REVIEWED_CERTIFICATES.json')
 out=compose(base,packet,reviewed)
 if a.write:a.write.write_text(json.dumps(out,indent=1)+'\n')
 result=dict(slice_rows=sum(r['row'] in read(E/'NED_SCOPE.json')['slice']['inventory_rows'] for r in out['rows']),closed=[r['row'] for r in out['rows'] if r['composed_status']=='CLOSED'],unchanged_native_bridge_status=True)
 print(json.dumps(result,indent=1))
if __name__=='__main__':main()
