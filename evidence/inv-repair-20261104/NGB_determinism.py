"""Resolve the identified set-order question with two fixed hash seeds."""
import pathlib,subprocess,sys,os,hashlib,json
E=pathlib.Path(__file__).resolve().parent
names=['NGB_ADMITTED_LEDGER.json.xz','NGB_OVERLAY.json','NGB_EDGES.json','NGB_CANDIDATES_RESOLVED.json','NGB_EXCLUDED.json']
runs=[]
for seed in ['1','2']:
 subprocess.run([sys.executable,str(E/'NGB_run.py'),'NGB_inventory.py'],env={**os.environ,'PYTHONHASHSEED':seed,'PYTHONDONTWRITEBYTECODE':'1'},check=True)
 runs.append(dict(seed=seed,sha256={n:hashlib.sha256((E/n).read_bytes()).hexdigest() for n in names}))
assert runs[0]['sha256']==runs[1]['sha256']
(E/'NGB_DETERMINISM.json').write_text(json.dumps(dict(reason='Stage-2 draft extended a propagation queue from an unordered set. Sorted traversal added; ensure OPEN occurrence IDs and all overlay outputs do not vary with Python hash randomization.',result='PASS',runs=runs),indent=1)+'\n')
