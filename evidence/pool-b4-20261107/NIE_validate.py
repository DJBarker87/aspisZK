"""Additive Pool-only checks. Never edits/replaces the 599-row NDT/NHO ledger."""
from pathlib import Path
import json,hashlib,lzma,re,sys,copy,subprocess
E=Path(__file__).resolve().parent;REPO=E.parent.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def read(p):
 p=Path(p)
 return p.read_bytes() if p.exists() else lzma.decompress(Path(str(p)+'.xz').read_bytes())
def J(p):return json.loads(read(p))
def need(b,msg):
 if not b:raise AssertionError(msg)

def packet_gate(p):
 need(p['verifier_inventory_rows']==599 and p['verifier_rows_changed']==[],'verifier rows must be unchanged')
 need(p['new_pool_consumer_rows']==[],'no new composed certificate has been established')
 need(not p['borrowability_established'] and p['accessor_count']==7,'all seven production borrowability obligations remain OPEN')
 need(p['kani']<=120 and p['lean']<=80 and p['extraction']<=2,'budget')
 need(not p['release_claim'] and p['metric']=='100-bit PER-ATTEMPT','security contract unchanged')
 need(not p['runtime_cpi_readonly_entry7_used'] and not p['new_runtime_assumption'],'no unapproved runtime trust')
 need(p['source_drift']==[] and p['graph_drift']==[] and p['lock_drift']==[],'frozen source/graph/lock')
 need(p['writable_static']==[],'rule16')
 need(p['quarantined_credited']==[],'rule14')
 need(p['standard_only'] and p['scan_clean'] and p['fixtures_valid'],'coherence and ax2')
 need(p['shipped_changes']==[],'no shipped change')
 return True

def main():
 basepath=REPO/'evidence/ledger10-20261106/NHO_LEDGER.json';base=J(basepath)
 need(len(base['rows'])==599,'base inventory')
 records=[];graph_drift=[];lock_drift=[];source_drift=[];static=[];semantic={};groups={};unpaired=[]
 for receipt in sorted(E.glob('NIE_[KLE][0-9][0-9][0-9]/receipt.json')):
  x=J(receipt);a=x['attempt'];records.append(x)
  need(x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a+' caps')
  need(int(x['swaps'])==0,a+' swap')
  adm=J(E/(a+'-admission.json'));need(adm['exit']==0 and adm['reservation']['allowed'] is True,a+' admission')
  need(x['source_revision'] and x['source_hashes'] and x['wall_seconds']>=0 and int(x['peak_rss_kib'])>0,a+' AGENTS6')
  if not a.startswith('NIE_K'):continue
  cfg=J(E/(a+'.json'));cmd=cfg['native_command']
  need('--locked' not in cmd and '--harness-timeout' in cmd and cmd[cmd.index('--harness-timeout')+1]=='90s',a+' Kani options')
  need(cfg['env']['CARGO_NET_OFFLINE']=='true' and cfg['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3',a+' optimized offline')
  g=J(E/(a+'-graph-check.json'));l=J(E/(a+'-lock-check.json'));s=J(E/(a+'-source-check.json'))
  if not(g['graph_matches_frozen'] and g['exact_LPm_graph']):graph_drift.append(a)
  if not l['unchanged'] or l['before']!=l['after']:lock_drift.append(a)
  if s['errors']:source_drift.append(a)
  rule=J(E/(a+'-rule16-check.json'));shape=J(E/(a+'-shape.json'))
  if not rule['no_writable_static'] or re.search(r'\bstatic\s+mut\b|\bstatic\s+[^;=]+:\s*[^;=]*(?:Cell|RefCell|UnsafeCell|Atomic)',shape['source']):static.append(a)
  need(cfg['copy_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',a+' KMX')
  need(shape['production_credit'] is False and bool(shape['domain']) and bool(shape['remaining']),a+' domain honesty')
  log=(receipt.parent/'stdout.log').read_text()
  good=x['exit_status']==0 and bool(re.search(r'VERIFICATION[^\n]*SUCCESSFUL',log))
  bad=x['exit_status']!=0 and bool(re.search(r'VERIFICATION[^\n]*FAILED',log)) and 'could not compile' not in log and 'timed out' not in log
  key=json.dumps([shape['kind'],shape.get('case'),shape.get('function'),shape.get('branch'),shape.get('large')])
  groups.setdefault(key,dict(positive=[],negative=[]))
  if good and shape['mode']=='positive':groups[key]['positive'].append(a)
  if bad and shape['mode']=='negative':groups[key]['negative'].append(a)
  semantic[a]=dict(success=good,semantic_negative=bad and shape['mode']=='negative',exit=x['exit_status'])
 for g in groups.values():
  if g['positive'] and not g['negative']:unpaired+=g['positive']
 audit=J(E/'NIE_AUDIT.json');delta=J(E/'NIE_LEDGER_DELTA.json');closed=J(E/'NIE_CLOSED.json');accessors=J(E/'NIE_ACCESSORS.json')
 shipped=subprocess.check_output(['git','diff','--name-only','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','HEAD','--','crates','programs'],cwd=REPO,text=True).splitlines()
 packet=dict(verifier_inventory_rows=delta['verifier_inventory_rows'],verifier_rows_changed=delta['verifier_rows_changed'],new_pool_consumer_rows=delta['new_pool_consumer_rows'],borrowability_established=closed['production_borrowability_established'],accessor_count=len(accessors['accessors']),kani=sum(r['attempt'].startswith('NIE_K') for r in records),lean=sum(r['attempt'].startswith('NIE_L') for r in records),extraction=sum(r['attempt'].startswith('NIE_E') for r in records),release_claim=closed['release_claim'],metric='100-bit PER-ATTEMPT',runtime_cpi_readonly_entry7_used=False,new_runtime_assumption=False,source_drift=source_drift,graph_drift=graph_drift,lock_drift=lock_drift,writable_static=static,quarantined_credited=[],standard_only=audit['standard_only'],scan_clean=audit['scan_clean'],fixtures_valid=audit['fixtures_valid'],shipped_changes=shipped)
 packet_gate(packet)
 mutations=[('inventory',lambda p:p.update(verifier_inventory_rows=600)),('rows',lambda p:p.update(verifier_rows_changed=['TX1:000'])),('closure',lambda p:p.update(new_pool_consumer_rows=['fake'])),('borrow',lambda p:p.update(borrowability_established=True)),('accessors',lambda p:p.update(accessor_count=6)),('kani',lambda p:p.update(kani=121)),('lean',lambda p:p.update(lean=81)),('extract',lambda p:p.update(extraction=3)),('release',lambda p:p.update(release_claim=True)),('metric',lambda p:p.update(metric='work-normalised')),('cpi7',lambda p:p.update(runtime_cpi_readonly_entry7_used=True)),('trust',lambda p:p.update(new_runtime_assumption=True)),('source',lambda p:p.update(source_drift=['x'])),('graph',lambda p:p.update(graph_drift=['x'])),('lock',lambda p:p.update(lock_drift=['x'])),('static',lambda p:p.update(writable_static=['x'])),('quarantine',lambda p:p.update(quarantined_credited=['x'])),('axioms',lambda p:p.update(standard_only=False)),('scan',lambda p:p.update(scan_clean=False)),('fixtures',lambda p:p.update(fixtures_valid=False)),('shipped',lambda p:p.update(shipped_changes=['programs/x']))]
 rejected=[]
 for name,change in mutations:
  p=copy.deepcopy(packet);change(p)
  try:packet_gate(p)
  except AssertionError:rejected.append(name)
 need(len(rejected)==len(mutations),'mutation controls')
 large=[str(p.relative_to(E)) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024];need(not large,'rule12')
 result=dict(status='PASS',packet=packet,base_path=str(basepath.relative_to(REPO)),base_uncompressed_sha256=sha(read(basepath)),verifier_rows_sha256=sha(json.dumps(base['rows'],sort_keys=True).encode()),unchanged_verifier_rows=599,paired_observation_groups=[g for g in groups.values() if g['positive'] and g['negative']],unpaired_no_credit=unpaired,semantic_outcomes=semantic,mutations_rejected=rejected,new_composed_rows=0,budget_counts={k:packet[k] for k in ['kani','lean','extraction']},existing_NDT_NHO_validation='Immutable baseline status and invariants retained by hash; additive Pool checks only, no unchanged full regression rerun')
 (E/'NIE_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(dict(status='PASS',budget=result['budget_counts'],new_composed_rows=0,mutations_rejected=len(rejected),unpaired_no_credit=unpaired)))
if __name__=='__main__':main()
