from pathlib import Path
import json,hashlib,lzma
E=Path(__file__).resolve().parent;N=E.parent/'native-decnat-20261028'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pairs=[('NDB_K007','NDB_K008','actual canonical digest, every32byte input'),('NDB_K029','NDB_K030','all Result arms and InvalidAccountData mapping'),('NDB_K037','NDB_K038','final empty-root predicate'),('NDB_K039','NDB_K040','tree header'),('NDB_K041','NDB_K042','lane header including lane-count conversion'),('NDB_K043','NDB_K044','format binding'),('NDB_K059','NDB_K060','one selected iterator write and all untouched coordinates')]
rows=[]
for a,b,meaning in pairs:
 evidence=[]
 for attempt,wanted in [(a,0),(b,1)]:
  p=N/attempt/'receipt.json';r=json.loads(p.read_text());assert r['exit_status']==wanted
  log=N/attempt/'stdout.log';raw=log.read_text() if log.is_file() else lzma.open(str(log)+'.xz','rt').read()
  assert ('VERIFICATION:- SUCCESSFUL' if wanted==0 else 'VERIFICATION:- FAILED') in raw
  if wanted:assert 'Failed Checks:' in raw and 'NDB semantic law' in raw
  graph=N/(attempt+'-graph.json');g=json.loads(graph.read_text())
  assert g['graph_matches_frozen'] and g['offline'] and g['lock_unchanged']
  assert g['lock_before_sha256']==g['lock_after_sha256']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  assert g['KMX_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
  root=[v for k,v in g['features'].items() if 'programs/r1-cost-probe#' in k];assert len(root)==1
  assert 'pool-adapter' in root[0] and 'private-leaf-salts' in root[0]
  source=json.loads((N/(attempt+'.json')).read_text());assert source['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  evidence.append({'attempt':attempt,'receipt_sha256':sha(p),'graph_sha256':sha(graph),'exit_status':r['exit_status'],'wall_seconds':r['wall_seconds'],'peak_rss_kib':r['peak_rss_kib'],'swaps':r['swaps'],'source_revision':r['source_revision'],'frozen_source':source['deps_fingerprint']['frozen_source'],'features':root[0]})
 rows.append({'law':meaning,'pair':evidence})
(E/'NMX_217_NDB_COMPONENTS.json').write_text(json.dumps({'validation':'source receipts, expected assertion failures, graph, feature parity, unchanged lock and exact KMX patch','pairs':rows},indent=2)+'\n')
print('Verified seven inherited native component/control pairs; no new native run')
