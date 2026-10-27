from pathlib import Path
import json,subprocess
E=Path('evidence/pv-integ1-20261027/d298');T=Path('tools/pv-integ3-20261027');H='dombarker@100.108.41.90';D='/home/dombarker/project-offloads/codex-pv-integ1-20261027/d298'
labels=json.loads((E/'fixture-labels.json').read_text())
(E/'baseline').mkdir(exist_ok=True)
subprocess.run(['python3',str(T/'collect.py'),*[(('baseline/' if side.startswith('baseline') else '')+label) for side,label in labels.items()]],check=True)
subprocess.run(['scp','-q',H+':'+D+'/fixture-comparison.json',str(E/'fixture-comparison.json')],check=True)
r=json.loads((E/'fixture-comparison.json').read_text());assert r['passed'],r
assert all(set(x['raw_result_differing_fields'])<= {'seconds'} for x in r['comparisons'])
(E/'fixture-scope.md').write_text('''D298 freshly built and ran both exact source revisions: 37e5e133f8 control
and 9ff5a4594e integrated candidate; transfer0 and withdrawal0, coin0, count1.
No proof/public/ledger disagreement. Result records use the established fixed
fixture comparator: canonical JSON excluding diagnostic elapsed seconds only.
Raw result.json equality is reported separately and is NOT claimed; changing
elapsed seconds is a diagnostic measurement difference, not a prover output
change. This matches D282 and batch1's previously recorded gate semantics.
A clarification was offered; no user override arrived before this comparison.
Two fixture pairs only; the 1,000-pair differential and timing remain unexecuted.
''')
subprocess.run(['git','add','--',str(E),str(T/'finish-stage3.py')],check=True)
subprocess.run(['git','commit','-m','Record D298 fixed coin fixture bytes against pre batch candidate','--',str(E),str(T/'finish-stage3.py')],check=True)
