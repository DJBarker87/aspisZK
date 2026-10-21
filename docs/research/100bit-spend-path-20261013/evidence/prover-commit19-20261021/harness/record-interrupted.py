"""Preserve an excluded scope interruption without inventing final metrics."""
from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent.parent
host='dombarker@100.108.41.90';H='/home/dombarker/project-offloads/codex-cx-prover-commit19-20261021';name='sim-insert-one-v1'
d=E/'receipts'/name;d.mkdir(parents=True,exist_ok=True)
for n in ['stdout.log','stderr.log','time.log']:
 subprocess.run(['scp',host+':'+H+'/receipts/'+name+'/'+n,str(d/n)],check=True)
subprocess.run(['scp',host+':'+H+'/'+name+'-inputs.json',str(E/(name+'-inputs.json'))],check=True)
x=dict(name=name,accepted=False,exact_target='sim::siminsert19::one_existing_entry',
 command=['cargo','kani','--no-assertion-reach-checks','-j','4','-p','aspis-r1-cost-probe','--features','r1p-check','--lib','--exact','--harness','sim::siminsert19::one_existing_entry','-Z','function-contracts','-Z','stubbing','-Z','unstable-options','--output-format','terse','--cbmc-args','--unwinding-assertions'],
 source_revision='28776b162',input_manifest=name+'-inputs.json',
 exit_status=None,scope_launcher_exit_status=241,wall_seconds=None,peak_rss_kib=None,swaps=None,
 observed_process_elapsed_lower_bound_seconds=239,observed_child_rss_kib=5906808,
 exclusion='Stopped own capped scope for proof-shape review before timeout. This also terminated the accounting wrapper, leaving time.log empty; no final wall/peak/swap metrics are claimed. Entire target excluded. Replacement narrows to overwrite only and lowers unwind 66 to 34.',
 print_axioms='N/A: excluded Kani interruption, no Lean result')
(d/'receipt.json').write_text(json.dumps(x,indent=2)+'\n')
f=E/'rust-attempts.json';rows=json.loads(f.read_text());rows=[r for r in rows if r['name']!=name]+[x];f.write_text(json.dumps(rows,indent=2)+'\n')
