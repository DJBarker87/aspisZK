"""Read-only verification of both archived source snapshots."""
import pathlib,json,hashlib,subprocess,datetime
H=pathlib.Path(__file__).resolve().parent
rows=[]
for who in ['candidate','research']:
 pins=json.loads((H/(who+'-source.json')).read_text());src=H/who/'src'
 mismatches=[p for p,s in pins['files'].items() if not (src/p).is_file() or hashlib.sha256((src/p).read_bytes()).hexdigest()!=s]
 rows.append(dict(label=who,meaning='merged candidate plus standalone lock repair' if who=='candidate' else 'pre-merge candidate control, not research',source_revision=pins['revision'],files=len(pins['files']),mismatches=mismatches))
(H/'source-verification.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),snapshots=rows,rustc=subprocess.check_output(['/home/dombarker/.cargo/bin/rustc','-Vv'],text=True)),indent=2)+'\n')
assert not any(r['mismatches'] for r in rows),rows
print(json.dumps(rows))
