#!/usr/bin/env python3
"""Additive call-domain certificate checks over a replayed NDT snapshot.

No local/model status is promoted by presence of a theorem name. A certificate
must bind the actual edge, frozen body, selected packets, all four association
parts, full Lean receipt/axioms, and the caller's inner-hypothesis discharge.
"""
from pathlib import Path
import argparse,copy,hashlib,importlib.util,json,lzma,re,subprocess,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent;N=E.parent/'native-ledger3-20261029'
sys.path[:0]=[str(N),str(E.parent/'native-ledger2-20261028')]
import NDT_validate as ndt
sha=lambda b:hashlib.sha256(b).hexdigest()
def obj(p):return json.loads(p.read_text())
def require(ok,message):
 if not ok:raise ValueError(message)

def check_receipt(cert,theorem):
 p=R/cert['receipt'];d=obj(p)
 require(sha(p.read_bytes())==cert['receipt_sha256'],'certificate receipt hash')
 require(d['exit_status']==0 and d['kind']=='lean','certificate Lean attempt did not pass')
 require(d['limits']==dict(zip(['memory.high','memory.max','memory.swap.max','pids.max'],['6442450944','8589934592','0','64'])),'certificate scope caps')
 require(d['swaps']=='0','certificate swap')
 require('-M7000' in d['command'],'certificate Lean cap')
 require(d['source_revision'] and d['wall_seconds']>=0 and d['peak_rss_kib'],'incomplete formal receipt')
 audit=next((a for a in d['print_axioms'] if a.startswith("'"+theorem+"' ")),None)
 require(audit is not None,'missing theorem axioms: '+theorem)
 axioms=re.search(r'depends on axioms: \[([^\]]*)\]',audit)
 require(not axioms or set(x.strip() for x in axioms[1].split(','))<=set(['propext','Classical.choice','Quot.sound']),'nonstandard axioms')
 for f,h in d['source_hashes'].items():
  raw=(p.parent/'sources'/f).read_bytes();require(sha(raw)==h,'receipt source hash')
  if f.endswith('.lean'):
   require(not re.search(r'\b(sorry|admit|axiom|native_decide)\b',raw.decode()),'forbidden proof construct')
 return d

def certificate_errors(edge,cert,baseline):
 """Fail closed; used both for ledger construction and mutation tests."""
 try:
  require(cert is not None,'missing call-domain certificate')
  require(cert['edge']==edge['edge'],'wrong certificate edge')
  require(cert['frozen_revision']==baseline['frozen_revision'],'wrong frozen source')
  require(cert['source_body_sha256']==edge['source_body_sha256'],'wrong caller body')
  require(cert['status']=='CLOSED','certificate not CLOSED')
  require(cert['kind'] in ['DIRECT_CALL','STATIC_UNREACHABLE'],'unknown certificate shape')
  rows=[r for r in baseline['rows'] if r['function']==edge['callee']]
  selected=sorted(set(c for r in rows for c in r['selected_claims']))
  require(cert['selected_callee_claims']==selected,'wrong selected callee packet')
  named=sorted(set(h['name'] for r in rows for h in r['named_hypotheses']))
  require(sorted(cert['inner_hypotheses_discharged'])==named,'missing/wrong inner named hypothesis')
  if cert['kind']=='STATIC_UNREACHABLE':
   require(edge['classification']=='CONSERVATIVE_ALTERNATIVE' and edge['selected_target'] is False,'target is not resolved away')
  else:
   require(edge['selected_target'] is not False,'direct call contradicts receiver resolution')
   for part in ['packet_domain','canonical_carrier','same_inputs_result','state_ordered_effects','physical_interpretation','native_callsite_association']:
    require(part in cert['parts'] and cert['parts'][part]['theorems'],'missing certificate part: '+part)
  require(cert['lean_evidence'],'missing certificate Lean evidence')
  audited=set()
  for item in cert['lean_evidence']:
   for theorem in item['theorems']:
    check_receipt(item,theorem);audited.add(theorem)
  require(cert['theorems'] and set(cert['theorems'])<=audited,'certificate theorem not audited')
  if cert['kind']=='DIRECT_CALL':
   require(all(set(v['theorems'])<=audited for v in cert['parts'].values()),'association part theorem not audited')
  require(set(cert['hypothesis_discharge_theorems'])==set(named),'missing inner discharge theorem association')
  require(all(set(v) and set(v)<=audited for v in cert['hypothesis_discharge_theorems'].values()),'inner hypothesis discharge theorem not audited')
  require(cert['residual_hypotheses']==[],'inner assumptions retained')
  require(cert['review']['conclusion_hiding'] is False,'conclusion hidden in certificate')
  require(cert['review']['statement_and_native_association_checked'] is True,'native association unreviewed')
  # The review is content-addressed and must exist as evidence, not a boolean.
  p=R/cert['review']['path'];require(sha(p.read_bytes())==cert['review']['sha256'],'association review hash')
  return []
 except (ValueError,KeyError,OSError,TypeError) as e:return [str(e)]

def extend(baseline,edges):
 # Preserve every original NDT structural/refresh/quarantine/feature check.
 ndt.validate_invariants(baseline)
 scope=obj(E/'NEB_SCOPE.json')['slice']
 require({e['edge'] for e in edges['edges']}==set(scope['internal_edges']),'missing/extra slice edge')
 require(len(edges['edges'])==len(scope['internal_edges']),'duplicate edge')
 require(all(e['caller']+' -> '+e['callee']==e['edge'] for e in edges['edges']),'edge identity')
 for e in edges['edges']:
  callers=[r for r in baseline['rows'] if r['function']==e['caller']]
  require(callers and all(r['frozen_body_sha256']==e['source_body_sha256'] for r in callers),'edge source body mismatch')
  require(all(any(o['id']==e['obligation_id'] and o.get('callee')==e['callee'] for o in r['caller_domain_obligations']) for r in callers),'edge obligation mismatch')
 from NEB_certificates import expected
 approved_edges,approved_rows=expected(baseline)
 # Additional ORIGINAL inventory self-obligations are kept explicit. They
 # were omitted only from the slice's self-edge-free enumeration.
 from NEB_additive_certificates import expected as additive_expected
 _,_,approved_inventory=additive_expected(baseline)
 inventory_edges=edges.get('inventory_edges',[])
 require(len({e['obligation_id'] for e in inventory_edges})==len(inventory_edges),'duplicate inventory edge')
 approved_index={e['obligation_id']:e for e in approved_inventory}
 for e in inventory_edges:
  require(e['obligation_id'] in approved_index,'unregistered extra inventory obligation')
  require({k:v for k,v in e.items() if k not in ['certificate','status','obstacle']}=={k:v for k,v in approved_index[e['obligation_id']].items() if k not in ['certificate','status','obstacle']},'wrong extra inventory edge')
  require(e['caller']==e['callee'] and e['classification']=='CONSERVATIVE_ALTERNATIVE' and e['selected_target'] is False,'extra inventory edge is not resolved self-target')
 out=copy.deepcopy(baseline);changes=[]
 rowcerts={c['row']:c for c in edges.get('row_certificates',[])}
 require(len(rowcerts)==len(edges.get('row_certificates',[])),'duplicate row certificate')
 # Never erase conservative targets or original obligations. A pruning
 # certificate closes the obligation explicitly, retaining the inventory row.
 index={e['obligation_id']:e for e in edges['edges']+inventory_edges}
 require(len(index)==len(edges['edges'])+len(inventory_edges),'inventory/slice obligation collision')
 for row in out['rows']:
  if row['function'] not in scope['functions']:continue
  for obligation in row['caller_domain_obligations']:
   edge=index.get(obligation['id'])
   if edge is None:continue
   errors=certificate_errors(edge,edge.get('certificate'),baseline)
   if not errors and edge.get('certificate')!=approved_edges.get(edge['edge']):errors=['unregistered or wrong concrete certificate']
   if not errors:
    obligation.update(status='CLOSED',discharged_by=edge['certificate']['id'])
  # Existing NDT semantics remain necessary. The edge extension alone cannot
  # discharge an inventory domain or a row's own named hypothesis.
  rc=rowcerts.get(row['row'])
  if rc is not None:
   require(rc==approved_rows.get(row['row']),'unregistered or wrong concrete row certificate')
   require(rc['function']==row['function'] and rc['frozen_body_sha256']==row['frozen_body_sha256'],'wrong row certificate')
   require(rc['selected_claims']==row['selected_claims'] and rc['selected_claims'],'wrong row bridge selection')
   require(sorted(rc['named_hypotheses_discharged'])==sorted(h['name'] for h in row['named_hypotheses']),'row named hypothesis mismatch')
   require(sorted(rc['inventory_domains_discharged'])==sorted(o['unit'] for o in row['inventory_domain_obligations']),'inventory domain mismatch')
   require(rc['lean_evidence'] and rc['parts']==['result','state','ordered_effects','native_association'],'row association incomplete')
   require(rc['remaining_inner_hypotheses']==[],'row hides inner hypothesis')
   allowed=[row['function']+'.PacketDomain',row['function']+'.PhysicalInterpretation']+[t['id'] for t in baseline['trust_rows']]+['RuntimePersistence','CompositionTrustOptionA']
   require(set(rc['top_hypotheses'])<=set(allowed),'unapproved root hypothesis')
   for item in rc['lean_evidence']:
    for theorem in item['theorems']:check_receipt(item,theorem)
   review=R/rc['review']['path'];require(sha(review.read_bytes())==rc['review']['sha256'],'row statement/native review hash')
   # Every transitive OPEN target must have its own admitted row certificate.
   # A certificate name alone never clears a dependency.
   need=set(row['open_transitive_dependencies'])
   require(not need or need<=set(c['function'] for c in rowcerts.values()),'missing dependency certificate')
   for h in row['named_hypotheses']:h['discharged_by']=rc['id']
   for o in row['inventory_domain_obligations']:o.update(status='CLOSED',discharged_by=rc['id'])
   for o in row['caller_domain_obligations']:
    if 'call' in o:
     ext=rc['external_obligations'].get(o['id'])
     require(ext is not None,'external obligation unproved')
     if ext['kind']=='TRANSPARENT_M31_CONSTRUCTOR':
      require(o['call'].get('expression',o['call'].get('syntax'))=='M31' and ext['syntax']=='M31','wrong external constructor')
      o.update(status='CLOSED',discharged_by=rc['id']+':constructor')
     elif ext['kind']=='RELEASE_CFG_INACTIVE':
      require(o['call'].get('resolution')=='disabled release cfg','inactive cfg is not original inventory classification')
      require(ext['cfg']==o['call']['cfg'] and ext['cfg'] and ext['selected_core_features']==['r0'],'wrong inactive feature projection')
      require(ext['native_review']==rc['native_review'],'inactive cfg lacks same native feature review')
      require(any(any('feature = \"'+f+'\"' in c for f in ['r0-op-count','r0-r91-audit','r0-e4-reference']) for c in ext['cfg']),'cfg inactivity not established')
      o.update(status='CLOSED',discharged_by=rc['id']+':inactive-release-cfg')
     else:require(False,'unregistered external obligation kind')
 # Admit rows bottom-up along actual obligations. Resolved-away alternatives
 # remain CLOSED obligations but are not active call dependencies. No real SCC
 # is closed without a separately supplied induction certificate.
 changed=True
 while changed:
  changed=False
  by_function={}
  for r in out['rows']:by_function.setdefault(r['function'],[]).append(r)
  for row in out['rows']:
   if row['row'] not in rowcerts or row['composed_status']=='CLOSED':continue
   all_obligations=all(o['status']=='CLOSED' and o['discharged_by'] for o in row['caller_domain_obligations'])
   if not all_obligations:continue
   active=[]
   for o in row['caller_domain_obligations']:
    if 'callee' not in o:continue
    e=index.get(o['id']);c=e.get('certificate') if e else None
    if c and c['kind']=='STATIC_UNREACHABLE':continue
    active.append(o['callee'])
   ready=all(by_function.get(f) and all(r['composed_status']=='CLOSED' for r in by_function[f]) for f in active)
   if not ready:continue
   closed=(row['selected_claims'] and
     all(h['discharged_by'] for h in row['named_hypotheses']) and
     all(o['status']=='CLOSED' and o['discharged_by'] for o in row['inventory_domain_obligations']))
   if closed:
    row['open_transitive_dependencies']=[]
    row.update(composed_status='CLOSED',composed_reason='Original snapshot gates preserved; all added content-addressed root and call-domain gates satisfied bottom-up')
    changes.append(row['row']);changed=True
 # NDK/NDT historical refresh additionally asserts all snapshot rows OPEN.
 # It was checked above against the immutable baseline. Applying it to a new
 # certificate result would prohibit *any* future composition. Preserve the
 # baseline and validate the extension separately; do not edit that assertion.
 for row in out['rows']:
  if row['composed_status']=='CLOSED':
   require(row['row'] in rowcerts,'CLOSED without root statement certificate')
   require(all(h['discharged_by'] for h in row['named_hypotheses']),'open row hypothesis')
   require(all(o['status']=='CLOSED' and o['discharged_by'] for o in row['caller_domain_obligations']),'open row call domain')
   require(not row['open_transitive_dependencies'],'open/quarantined transitive dependency')
   require(row['selected_claims'],'missing bridge')
 return out,dict(schema='NEB-ledger-delta-v1',composed_rows_closed=changes,closed_count=len(changes),slice='Q',roots={f:sorted(set(r['composed_status'] for r in out['rows'] if r['function']==f)) for f in scope['roots']},edge_closed=sum(not certificate_errors(e,e.get('certificate'),baseline) and e.get('certificate')==approved_edges.get(e['edge']) for e in edges['edges']),edge_total=len(edges['edges']),baseline_unchanged=True)

def replay_baseline():
 # NDT deliberately rejects previously unknown merged reports. Reconstruct its
 # exact historical snapshot, then separately require every current extra
 # report to have an explicit reviewed hash in NEB_CORPUS.json. No report is
 # silently ignored and none of NDT's original gates is removed.
 corpus=obj(E/'NEB_CORPUS.json');original=ndt.Store
 class HistoricalStore(original):
  def __init__(self):
   super().__init__()
   reports=lambda paths:{p for p in paths if p.endswith('.md') and not p.startswith(ndt.OUT) and (p.startswith(ndt.DESIGN) or ('/evidence/' in '/'+p and p.split('evidence/',1)[1].count('/')==1))}
   old=reports(self.tree);current=reports(self.head_tree)
   require(old<=current,'inherited report removed')
   require(current-old==set(corpus['additional_reports']),'new report requires explicit corpus review')
   for p,h in corpus['additional_reports'].items():
    raw=self.blob('HEAD:'+p);require(sha(raw)==h,'additional report changed: '+p)
    if (R/p).exists():require(sha((R/p).read_bytes())==h,'dirty additional report: '+p)
   require(all(self.head_tree.get(p)==v[0] for p,v in self.tree.items()),'an inherited Git file changed; historical replay cannot hide it')
   dirty=set(ndt.git('diff','--name-only','HEAD').decode().splitlines())
   require(not (dirty & set(self.tree)),'dirty inherited file before historical replay')
   self.head_tree={p:v[0] for p,v in self.tree.items()}
 ndt.Store=HistoricalStore
 try:rebuilt=ndt.collect()
 finally:ndt.Store=original
 original_ledger=obj(N/'NDT_LEDGER.json')
 require(rebuilt==original_ledger,'original NDT evidence replay changed')
 return rebuilt

def main():
 p=argparse.ArgumentParser();p.add_argument('--write',action='store_true');p.add_argument('--replay-baseline',action='store_true');p.add_argument('--write-ledger',action='store_true');a=p.parse_args()
 baseline=replay_baseline() if a.replay_baseline else obj(N/'NDT_LEDGER.json')
 scope=obj(E/'NEB_SCOPE.json');require(sha((N/'NDT_LEDGER.json').read_bytes())==scope['ledger_sha256'],'changed authoritative ledger')
 out,delta=extend(baseline,obj(E/'NEB_EDGES.json'))
 if a.write_ledger:
  raw=ndt.dump(out).encode();(E/'NEB_LEDGER.json.xz').write_bytes(lzma.compress(raw,preset=6));(E/'NEB_LEDGER.json.sha256').write_text(sha(raw)+'  NEB_LEDGER.json\n')
 if a.write:(E/'NEB_LEDGER_DELTA.json').write_text(json.dumps(delta,indent=1)+'\n')
 else:require(delta==obj(E/'NEB_LEDGER_DELTA.json'),'ledger delta differs from checked certificates')
 print(json.dumps(delta,indent=1))
if __name__=='__main__':
 try:main()
 except (AssertionError,ValueError,KeyError,OSError) as e:print('NEB validation FAILED: '+str(e),file=sys.stderr);sys.exit(1)
