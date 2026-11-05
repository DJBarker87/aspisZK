"""Add checks only; zero-promotion identity delta over pinned NHO + NHS.
No predecessor mutation, graph pruning, trust removal, or prover replay.
"""
from pathlib import Path
import json,hashlib,lzma,subprocess,re,copy
E=Path(__file__).resolve().parent;R=E.parents[1]
H=lambda b:hashlib.sha256(b).hexdigest()
J=lambda p:json.loads(Path(p).read_bytes())
STD={'propext','Classical.choice','Quot.sound'}
LIMITS={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
def receipt(a,exit):
 r=J(E/a/'receipt.json');ad=J(E/(a+'-admission.json'))
 assert r['exit_status']==exit and r['limits']==LIMITS and int(r['swaps'])==0
 assert ad['exit']==0 and ad['reservation']['allowed']is True
 for n,h in r['source_hashes'].items():assert H((E/a/'sources'/n).read_bytes())==h,(a,n)
 return r

def gates(delta,closed,audit):
 assert delta['checks_removed']==0 and delta['newly_closed']==[] and delta['new_rows']==delta['new_functions']==0
 assert not delta['canonical_graph_changed'] and delta['unchanged_other_statuses'] and not delta['target_established']
 assert closed['newly_closed']==[] and closed['status']=='SUPPORT_ONLY'
 assert [(r['row'],r['status']) for r in closed['functions']]==[('TX1:087','OPEN'),('TX1:094','OPEN')]
 assert closed['writer_route']=='checked existing-headline extraction route only; no direct transport/extraction premise removed'
 assert audit['status']=='PASS' and audit['raw_roots']==47 and audit['all_raw_roots_standard'] and audit['raw_collect_agree']
 assert audit['scan_exit']==audit['dangling']==audit['incompatible_owners']==audit['import_mismatches']==0
 assert len(audit['results'])==47 and all(r['equal'] and set(r['walked_axioms'])<=STD for r in audit['results'])

def main():
 delta=J(E/'NHW_LEDGER_DELTA.json');closed=J(E/'NHW_CLOSED.json');audit=J(E/'NHW_AUDIT.json');gates(delta,closed,audit)
 for p,h in J(E/'NHW_VALIDATOR_PINS.json').items():assert H(subprocess.check_output(['git','show','HEAD:'+p],cwd=R))==h
 raw=lzma.decompress((R/delta['baseline']).read_bytes());assert H(raw)==delta['baseline_sha256']
 baseline=json.loads(raw);before={r['row']:r['composed_status'] for r in baseline['rows']};assert len(before)==599
 inherited=J(R/delta['inherited_delta']);assert inherited['newly_closed']==['TX1:179','TX1:186'] and inherited['checks_removed']==0
 assert J(R/'evidence/prepared-close-20261106/NHS_VALIDATION.json')['status']=='PASS'
 for row in inherited['newly_closed']:before[row]='CLOSED'
 after=copy.deepcopy(before)
 assert after==before and sum(v=='CLOSED' for v in after.values())==delta['counts_after']['CLOSED']==337
 assert sum(v=='OPEN' for v in after.values())==262
 for a in ['NHW_L029','NHW_L030','NHW_L031','NHW_L039','NHW_L040','NHW_L041','NHW_L043','NHW_L044','NHW_L045','NHW_L046','NHW_L047','NHW_L048','NHW_L049','NHW_L050','NHW_L051','NHW_L052','NHW_L053','NHW_L054','NHW_L055','NHW_L056']:
  r=receipt(a,0)
  assert 'sorryAx' not in str(r['print_axioms'])
 for a,status in [('NHW_K003',0),('NHW_K004',1)]:
  r=receipt(a,status);log=(E/a/'stdout.log').read_text();assert r['module']=='NHW_window::folded_root_window'
  assert 'VERIFICATION:- '+('FAILED' if status else 'SUCCESSFUL') in log
  assert 'timed out' not in log.lower() and 'unwinding assertion' not in log.lower()
  if status:assert re.search(r'\*\* 1 of \d+ failed',log) and 'assertion failed: good != cfg!(NHW_invert)' in log
  graph=J(E/(a+'-graph-check.json'));lock=J(E/(a+'-lock-check.json'))
  assert graph['graph_matches_frozen'] and lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  assert not J(E/(a+'-source-check.json'))['errors']
  assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  features=next(row['features'] for row in graph['all_crate_features'] if row['name']=='aspis-r1-cost-probe')
  assert {'default','private-leaf-salts','optimized-terminal','program-build'}<=set(features)
 assert J(E/'NHW_K003/receipt.json')['source_hashes']==J(E/'NHW_K004/receipt.json')['source_hashes']
 assert H((E/'NHW_KMX.patch').read_bytes())=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 roots=sum(J(E/'NHW_AUDIT_ROOTS.json')['groups'],[]);assert len(roots)==47 and set(roots)=={r['root']for r in audit['results']}
 fixtures=audit['fixtures'];assert len(fixtures)==8 and all(r['equal']for r in fixtures)
 for r in fixtures:
  if r['root'].startswith('NEP_Planted.'):assert len(r['walked_axioms'])==1
  else:assert r['walked_axioms']==[]
 scan=[json.loads(l)for l in (E/'NHW_LOADED_scan.jsonl').read_text().splitlines()]
 assert len(scan)==audit['modules']==13725 and all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in scan)
 source=(E/'NHW_WriterFromNative.lean').read_text();assert 'S2W_DigestExtraction.AeneasExtraction' in source and 'theorem under_retained_extraction' in source
 for n in J(E/'NHW_MODULES.json'):
  s=(E/(n+'.lean')).read_text();assert not re.search(r'(?m)^\s*(axiom|opaque).*:.*Prop|\bsorry\b|\badmit\b|\bnative_decide\b',s),n
  if n not in ['NHW_EmittedPrepare','NHW_EmittedTx1']:assert not re.search(r'set_option (maxHeartbeats|maxRecDepth)',s),n
 assert J(E/'NHW_REVALIDATED_REUSE.json')['status']=='PASS'
 freeze=J(E/'NHW_FROZEN.json');assert all(len(set(x.values()))==1 for x in freeze['trees'].values())
 denials=[]
 mutations=[('driver promotion',lambda d,c,a:d.update(newly_closed=['TX1:094'])),('prepare promotion',lambda d,c,a:c['functions'][0].update(status='CLOSED')),('removed validator check',lambda d,c,a:d.update(checks_removed=1)),('erased extraction boundary',lambda d,c,a:c.update(writer_route='direct closed')),('custom axiom',lambda d,c,a:a['results'][0].update(walked_axioms=['badAx'])),('scan mismatch',lambda d,c,a:a.update(import_mismatches=1))]
 for name,mutate in mutations:
  d,c,a=copy.deepcopy((delta,closed,audit));mutate(d,c,a)
  try:gates(d,c,a)
  except AssertionError:denials.append(name)
  else:raise AssertionError('accepted mutation '+name)
 out=dict(status='PASS',newly_closed=[],rows_preserved=599,checks_removed=0,mutations_rejected=denials,existing_validator_pins='NHW_VALIDATOR_PINS.json',canonical_status_map_sha256=H(json.dumps(after,sort_keys=True).encode()),raw_roots=47,modules=13725,trust_removed=False,target_established=False)
 (E/'NHW_VALIDATION.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(out))
if __name__=='__main__':main()
