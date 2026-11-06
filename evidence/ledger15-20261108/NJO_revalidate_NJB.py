from pathlib import Path
import json,hashlib,lzma
E=Path(__file__).resolve().parent;P=E.parent/'terminal-20261107'
aliases={r['path']:r['retained']for r in json.loads((P/'NJB_DEDUP.json').read_text())}
def data(n):
 p=P/n
 if p.exists():return p.read_bytes()
 if n in aliases:return data(aliases[n])
 if Path(str(p)+'.xz').exists():return lzma.decompress(Path(str(p)+'.xz').read_bytes())
 raise FileNotFoundError(n)
def J(n):return json.loads(data(n))
H=lambda b:hashlib.sha256(b).hexdigest();pins=[]
kmx=H(data('NJB_KMX.patch'));assert kmx=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
for a,expected in [('NJB_K005',0),('NJB_K002',1)]:
 r=J(a+'/receipt.json');log=data(a+'/stdout.log').decode()
 assert r['exit_status']==expected and ('VERIFICATION:- SUCCESSFUL'if expected==0 else'VERIFICATION:- FAILED')in log
 assert 'timed out'not in log.lower()and'error[E'not in log and not('unwinding assertion'in log.lower()and'FAILURE'in log)
 ad=J(a+'-admission.json');assert ad['exit']==0 and ad['reservation']['allowed']is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 g=J(a+'-graph-check.json');lock=J(a+'-lock-check.json');src=J(a+'-source-check.json')
 assert g['graph_matches_frozen']and not g['new_package_tuples']and not g['edge_errors']and not src['errors']
 assert lock['unchanged']and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
 assert r['env']['CARGO_NET_OFFLINE']=='true'and '--locked'not in r['native_command']
 features=r['native_command'][r['native_command'].index('--features')+1];assert 'r0'in features and 'pool-v1-kernel'in features and 'no-entrypoint'not in features
 config=J(a+'.json');assert 'NJB_KMX.patch'in config['sources']
 for n in ['NJB_KMX.patch',a+'/receipt.json',a+'/stdout.log',a+'-graph-check.json',a+'-lock-check.json',a+'-source-check.json',a+'.json']:
  pins.append(dict(path=str(P/n),sha256=H(data(n)),bytes=len(data(n))))
shipped=J('NJB_SHIPPED_CHECK.json');assert all(r['frozen_tree']==r['head_tree']and not r['dirty']for r in shipped['trees'])
(E/'NJO_NJB_REVALIDATION.json').write_text(json.dumps(dict(status='PASS',row='TX1:268',pair=['NJB_K005','NJB_K002'],KMX=kmx,graph='frozen',lock='unchanged',features=features,pins=pins),indent=1)+'\n')
print('NJB getter native/control, deployed statement features, frozen graph/lock and exact KMX PASS')
