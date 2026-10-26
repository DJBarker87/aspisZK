from pathlib import Path
import json,re,hashlib
p=Path('docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/entropy-kernel64')
rows=[]
for a in list(range(11480,11500))+[11576,11578,11579,11580,11581]:
 x=json.loads((p/f'{a}-input.json').read_text());s=(p/f'{a}.lean.txt').read_bytes();assert hashlib.sha256(s).hexdigest()==x['source_sha256']
 o=(p/f'out{a}.log').read_text();tf=p/f'time{a}.log';t=tf.read_text() if tf.exists() else ''
 status=re.search(r'Exit status: (\d+)',t)
 x.update(exit_status=int(status[1]) if status else None,time_log=t,print_axioms=[l for l in o.splitlines() if 'axioms' in l],errors=[l for l in o.splitlines() if 'error:' in l],command=f"sh {x['launcher']} {a} {x['module']} J 7000 7 {x['deps_fingerprint']}")
 if a==11581:x.update(disposition='Resource reservation rejected before Lean; no wall/RSS/axioms exist',reservation=dict(allowed=False,bounded_reserved_bytes=51942260736,projected_reserved_bytes=59458453504,safe_limit_bytes=59055800320,requested_bytes=7516192768))
 if x['exit_status']==0:assert 'sorryAx' not in o
 (p/f'{a}-receipt.json').write_text(json.dumps(x,indent=2)+'\n')
 rows.append(dict(attempt=a,module=x['module'],exit_status=x['exit_status'],wall=re.findall(r'Elapsed .*: (.*)',t),peak_rss_kib=re.findall(r'Maximum resident set size \(kbytes\): (.*)',t),swaps=re.findall(r'Swaps: (.*)',t)))
(p/'summary.json').write_text(json.dumps(dict(base_revision='5b5ff8df24',input_label_correction='11480-11482 labels ef9295f1b7-WIP; actual base 5b5ff8df24; exact source and dependency hashes retained',attempts=rows,compiles=sum(x['exit_status'] is not None for x in rows),passed=sum(x['exit_status']==0 for x in rows),failed=sum(x['exit_status'] not in (None,0) for x in rows),not_launched=[11577],resource_preflight_rejections=[11581]),indent=2)+'\n')
print([(x['attempt'],x['exit_status']) for x in rows])
