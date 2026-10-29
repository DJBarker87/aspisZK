from pathlib import Path
import subprocess,json,sys
H=Path('/home/dombarker/project-offloads/codex-pv-b3q-20261029');mode=sys.argv[1]
if mode=='positive':
 cmd=['cargo','+1.94.1','run','--release','--locked','--offline','--manifest-path',str(H/'d188/Cargo.toml'),'--bin','d188-b3q','--jobs','4']
else:cmd=[str(H/'target/release/d188-b3q'),'--negative']
r=subprocess.run(cmd,text=True,stdout=subprocess.PIPE);(H/('d188-'+mode+'-raw.jsonl')).write_text(r.stdout)
if r.returncode:raise SystemExit(r.returncode)
actual={}
for line in r.stdout.splitlines():
 if not line.startswith('{'):continue
 row=json.loads(line);key=row['function']+':'+str(row['seed']);assert key not in actual,key;actual[key]=row['limbs']
expected=json.loads((H/'d188-expected.json').read_text());mismatches=[k for k in sorted(expected.keys()|actual.keys())if expected.get(k)!=actual.get(k)]
x=dict(mode=mode,expected_rows=len(expected),actual_rows=len(actual),mismatches=mismatches,evidence_class='finite native-versus-emitted-model comparisons; no universal native equality claimed')
(H/('d188-'+mode+'-comparison.json')).write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x))
raise SystemExit(1 if mismatches else 0)
