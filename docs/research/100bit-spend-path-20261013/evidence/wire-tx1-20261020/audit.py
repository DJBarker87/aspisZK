from pathlib import Path
import hashlib,json,re
p=Path(__file__).resolve().parent; root=p.parents[4]
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
def reports(log):return [' '.join(x.split()) for x in re.findall(r"^('[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms))",log,re.M|re.S)]
manifest=json.loads((p/'manifest.json').read_text()); records={}
for receipt in sorted(p.glob('*/*/receipt.json')):
 r=json.loads(receipt.read_text());r['axioms']=reports((receipt.parent/'lean.log').read_text())
 receipt.write_text(json.dumps(r,indent=2)+'\n');records[(r['module'],r['source_sha256'])]=(receipt,r)
for n,r in enumerate(manifest['attempts']):manifest['attempts'][n]=records[(r['module'],r['source_sha256'])][1]
final=[]
for src in sorted((p.parents[1]/'lean').glob('WireTx1*.lean')):
 rpath,r=records[(src.stem,sha(src))];assert r['exit_status']==0 and not r['errors']
 expected=re.findall(r'^#print axioms (\S+)',src.read_text(),re.M)
 assert len(expected)==len(r['axioms']),(src,expected,r['axioms'])
 for line in r['axioms']:
  if 'depends on axioms:' in line:
   axioms=set(re.search(r'\[([^\]]*)\]',line)[1].replace(' ','').split(','))
   assert axioms <= {'propext','Classical.choice','Quot.sound'},line
 for dep in r['direct_imports']:assert sha(Path(dep['object_path']))==dep['object_sha256'],dep
 obj=Path('/tmp/cx-wire-tx1-objects')/(src.stem+'.olean')
 assert not re.search(r'^\s*(axiom|sorry|admit)\b|native_decide|set_option\s+(maxRecDepth|maxHeartbeats)',src.read_text(),re.M)
 final.append(dict(module=src.stem,source_sha256=sha(src),receipt=str(rpath.relative_to(root)),receipt_sha256=sha(rpath),audits=len(expected),wall_seconds=r['wall_seconds'],peak_rss_bytes=r['peak_rss_bytes'],swaps=r['process_swap_count'],object_sha256=sha(obj),object_size_bytes=obj.stat().st_size))
inv=json.loads((p/'source-inventory.json').read_text())
for pin in inv['pins']:assert sha(root/pin['path'])==pin['sha256'],pin
assert sum(s['cone']=='tx1' for s in inv['digest_sites'])==31
manifest['final_successes']=final; manifest['audit']='audit.json';(p/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
audit=dict(status='pass',scope='Focused source/receipt and direct-import audit; no clean release replay',final_successes=final,final_theorem_audits=sum(r['audits'] for r in final),attempt_count=len(manifest['attempts']),source_inventory_sha256=sha(p/'source-inventory.json'),final_wall_seconds=sum(r['wall_seconds'] for r in final),final_peak_rss_bytes=max(r['peak_rss_bytes'] for r in final))
(p/'audit.json').write_text(json.dumps(audit,indent=2)+'\n');print(json.dumps(audit,indent=2))
