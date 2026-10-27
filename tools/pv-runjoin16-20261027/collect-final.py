from pathlib import Path
import subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin16-20261027';host='dombarker@100.108.41.90';H='/home/dombarker/project-offloads/codex-pv-runjoin-20261026/gate13/candidate'
if not (E/'gate-a-hoist-only.json').exists():(E/'gate-a-hoist-only.json').write_bytes((E/'gate-a.json').read_bytes())
label=sys.argv[1] if len(sys.argv)>1 else 'final'
rev=sys.argv[2] if len(sys.argv)>2 else 'dc8f3093d8'
rev=subprocess.check_output(['git','rev-parse',rev],text=True).strip()
results=[]
for mode in ['default','devnet','pool']:
 out=E/(label+'-'+mode);out.mkdir(exist_ok=True)
 for p in ['comparison.json','command.json','reservation.json','reservation.log']:
  subprocess.run(['scp','-q',host+':'+H+'/pv16-'+label+'-'+mode+'/'+p,str(out)],check=True)
 if not (out/'receipt').exists():subprocess.run(['scp','-qr',host+':'+H+'/pv16-'+label+'-'+mode+'/receipt',str(out)],check=True)
 p=out/'receipt/receipt.json';d=json.loads(p.read_text());d.update(source_revision=rev,axioms='N/A: SBF compilation, no Lean theorem');p.write_text(json.dumps(d,indent=2)+'\n')
 results.append(json.loads((out/'comparison.json').read_text()))
assert all(r['matches'] for r in results)
(E/'gate-a.json').write_text(json.dumps(results,indent=2)+'\n')
p=E/'large-llbc-artifacts.json';rows=json.loads(p.read_text())
for q in E.glob('*.llbc'):
 rows.append(dict(name=q.name,sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size,host_path='/home/dombarker/project-offloads/codex-pv-runjoin-20261026/evidence/'+q.name,retained_on_host=True));q.unlink()
p.write_text(json.dumps(rows,indent=2)+'\n')
rows=[]
for p in sorted(E.glob('pv16-records-*/receipt.json')):
 d=json.loads(p.read_text());rows.append(dict(receipt=str(p.relative_to(R)),target=d['target'],exit=d['exit'],wall_seconds=d['wall_seconds'],peak_rss_bytes=d['peak_rss_bytes'],swaps=d['swaps'],source_revision=d.get('source_revision'),axioms=d['axioms']))
(E/'receipt-index.json').write_text(json.dumps(rows,indent=2)+'\n')
