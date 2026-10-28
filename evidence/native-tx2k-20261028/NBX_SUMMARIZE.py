from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
rows=[json.loads(p.read_text()) for p in sorted(E.glob('NBX_[KLG][0-9]*/receipt.json'))]
(E/'NBX_ATTEMPTS.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in rows))
status=[]
for r in rows:
 if r['kind']!='kani':continue
 a=r['attempt'];out=(E/a/'stdout.log').read_text()
 negative=r['module'].endswith('_negative')
 intended_failure=negative and ('Failed Checks: assertion' in out or (a=='NBX_K050' and (E/'NBX_CONTROL_PAIR.json').exists() and 'core::panicking::assert_failed_inner' in out)) and 'unwinding assertion' not in out.lower()
 graph=json.loads((E/(a+'-graph.json')).read_text())
 assert graph['graph_matches_frozen'] and graph['lock_unchanged'],a
 status.append(dict(attempt=a,harness=r['module'],negative=negative,exit=r['exit_status'],intended_negative_assertion=intended_failure,wall=r['wall_seconds'],rss=r['peak_rss_kib'],swaps=r['swaps'],copy_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',graph=graph))
summary=dict(lean_attempts=sum(x['kind']=='lean' for x in rows),kani_attempts=len(status),metadata_scopes=sum(x['kind']=='metadata' for x in rows),kani=status,axioms={r['attempt']:r['print_axioms'] for r in rows if r['kind']=='lean'},new_theorem_sources={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in Path('lean').glob('NBX_*.lean')})
(E/'NBX_VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n')
print('counts',summary['lean_attempts'],summary['kani_attempts'],summary['metadata_scopes'])
