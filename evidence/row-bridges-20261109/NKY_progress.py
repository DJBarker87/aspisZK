from pathlib import Path
import json
E=Path(__file__).resolve().parent
files=sorted((E/'NKY_audit').glob('batch*/proof*.json'));results=[r for p in files for r in json.loads(p.read_text())['results']]
a={'propext','Classical.choice','Quot.sound'}
print(json.dumps(dict(groups=len(files),roots=len(results),nonstandard=[r['root']for r in results if not set(r['walked_axioms'])<=a],collector_disagreements=[r['root']for r in results if not r['equal']])))
