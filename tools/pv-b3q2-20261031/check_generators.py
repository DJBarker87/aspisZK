from pathlib import Path
import tempfile,subprocess,os,hashlib,json
D=Path('evidence/pv-b3q2-20261031');actual=D/'lean';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
with tempfile.TemporaryDirectory(prefix='pv-b3q2-generators-')as name:
 out=Path(name);(out/'lean').mkdir();env=dict(os.environ,PV_B3Q_OUTPUT=name)
 for s in ['tables.py','aggregate_tables.py','function_guards.py']:
  subprocess.run(['python3',str(Path('tools/pv-b3q2-20261031')/s)],env=env,check=True,stdout=subprocess.PIPE)
 rows=[dict(module=p.stem,generated_sha256=sha(p),source_sha256=sha(actual/p.name),match=sha(p)==sha(actual/p.name))for p in sorted((out/'lean').glob('*.lean'))]
 assert len(rows)==56,len(rows)
 assert all(r['match']for r in rows)
 (D/'generator-checks.json').write_text(json.dumps(dict(mode='--check equivalent: isolated regeneration without overwriting sources',files=rows,all_match=True),indent=2)+'\n')
 print(json.dumps(dict(checked=len(rows),all_match=True)))
