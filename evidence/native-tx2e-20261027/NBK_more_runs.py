from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
# Run only after all original source-window positions are terminal and passing.
for i in range(1,41):
 a=f'NBK_K{i:03}';x=json.loads((E/a/'receipt.json').read_text());g=json.loads((E/(a+'-graph.json')).read_text())
 assert x['exit_status']==0 and g['lock_unchanged'] and g['graph_matches_frozen'],a
for a,h in json.loads((E/'NBK_MORE_JOBS.json').read_text()):
 assert not (E/a/'receipt.json').exists(),a
 if a=='NBK_K060':
  audit=json.loads((E/'NBK_L048/receipt.json').read_text());assert audit['exit_status']==0
  assert all('sorryAx' not in x for x in audit['print_axioms'])
 r=subprocess.run(['python3',str(E/'NBK_native.py'),'run',a,'pool_v1::pair_terminal::NBK_more::'+h])
 if r.returncode:sys.exit(r.returncode)
