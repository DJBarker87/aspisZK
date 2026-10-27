from pathlib import Path
import json,subprocess
E=Path('evidence/pv-integ1-20261027/d298');T=Path('tools/pv-integ3-20261027');H='dombarker@100.108.41.90';D='/home/dombarker/project-offloads/codex-pv-integ1-20261027/d298'
labels=json.loads((E/'client-labels.json').read_text())
subprocess.run(['python3',str(T/'collect.py'),*labels.values()],check=True)
O=E/'binary-route';O.mkdir(exist_ok=True)
for name in ['route-symbols.json','route-disassembly.txt','op223-site.json','meta.json']:
 subprocess.run(['scp','-q',H+':'+D+'/binary-route/'+name,str(O/name)],check=True)
pins=json.loads((E/labels['client']/'binary-pins.json').read_text())['devnet_spend'];routes=json.loads((O/'route-symbols.json').read_text());op=json.loads((O/'op223-site.json').read_text())
assert any('generate_for_mask_nonce' in r['symbol'] and r['resolved_reachable'] for r in routes)
assert any('prover_shared::compress_tagged_tuple' in r['symbol'] and r['resolved_reachable'] for r in routes)
(E/'client-summary.json').write_text(json.dumps(dict(source_revision='9ff5a4594ec1cad5b5d12c7cb5a49270f9b098e3',label='recommended recipe pending owner approval; toolchain unpinned',**pins,toolchain=(E/labels['client']/'toolchain.txt').read_text(),generate_for_mask_nonce_reachable=True,op223_compress_tagged_tuple_reachable=True,op223_source_call=op['call'],op223_source_line=op['line'],limitations='Resolved static direct/GOT-edge reachability in the actual optimized ELF; does not establish executable/model adequacy or privacy endpoint'),indent=2)+'\n')
subprocess.run(['git','add','--',str(E),str(T/'finish-stage2.py')],check=True)
subprocess.run(['git','commit','-m','Record D298 recommended client build and route symbols','--',str(E),str(T/'finish-stage2.py')],check=True)
