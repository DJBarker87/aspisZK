from pathlib import Path
import json, hashlib, subprocess
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
accepted={'LPr_WordValue':11,'LPr_WordNat':12,'LPr_SelectedBytes':14,'LPr_SelectedWords':15,'LPr_Audit':16}
rows=[]
for module,n in accepted.items():
 a=f'LPr_L{n:03d}';r=json.loads((E/a/'receipt.json').read_text())
 src=Path('lean')/(module+'.lean');snapshot=E/a/'sources'/'LPr_generated'/(module+'.lean')
 assert sha(src)==sha(snapshot)
 assert r['exit_status']==0
 assert all('sorryAx' not in x and '_native.' not in x for x in r['print_axioms'])
 rows.append(dict(module=module,sha256=sha(src),attempt=a,receipt=r))
base=subprocess.check_output(['git','rev-parse','b635e25f4b^'],text=True).strip()
changed=subprocess.check_output(['git','diff','--name-only',base],text=True).splitlines()
assert all(x.startswith('lean/LPr_') or x.startswith('evidence/leaf-p6-16-20261027/') for x in changed)
allruns=[json.loads(p.read_text()) for p in sorted(E.glob('LPr_L*/receipt.json'))]
assert len(allruns)==16
out=dict(status='OPEN',base=base,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),dirty=True,
 lean_attempts=16,round_lean_limit=40,kani_runs=0,round_kani_limit=10,
 exit_zero=sum(r['exit_status']==0 for r in allruns),excluded_exit_zero=['LPr_L005'],
 missing_unchanged_dependencies=91,accepted=rows,
 max_rss_kib=max(int(r['peak_rss_kib']) for r in allruns),swaps=[r['swaps'] for r in allruns],
 scope='7 helper theorem roots; not the complete prepared_claim leaf or a release manifest',changed_tracked=changed)
(E/'LPr_FINAL_AUDIT.json').write_text(json.dumps(out,indent=2)+'\n')
