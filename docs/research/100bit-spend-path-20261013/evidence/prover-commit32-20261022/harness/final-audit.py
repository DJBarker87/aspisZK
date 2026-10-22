#!/usr/bin/env python3
"""Audit the exact final proof bytes, accepted axioms, and frozen source pins."""
from pathlib import Path
import json,hashlib,re,subprocess
E=Path(__file__).resolve().parent.parent
L=Path('docs/research/v8-r0-zk-20261009/lean')
accepted={'AspisR1IndexInsert32.Types':9021,'AspisR1IndexInsert32.Funs':9022,
 'AspisR1Publish32.Types':9023,'AspisR1Publish32.Funs':9024,
 'AspisR1Program32.Types':9033,'AspisR1Program32.Funs':9035,
 'R1Z.ProverCommitPublication32':9032,'R1Z.ProverCommitSorted32':9040,
 'R1Z.ProverCommitProgram32':9039,'R1Z.ProverCommitMapInvariant32':9043}
checks=[]
records={r['attempt']:r for r in json.loads((E/'lean/attempts.json').read_text())}
for module,attempt in accepted.items():
 p=L/(module.replace('.','/')+'.lean');sha=hashlib.sha256(p.read_bytes()).hexdigest()
 r=records[attempt]
 assert r['source_sha256']==sha,(module,attempt,'source drift')
 assert r['exit_status']==['0'],r
 lines=r['print_axioms'];assert all('sorryAx' not in line for line in lines)
 for line in lines:
  axioms=re.search(r'axioms: \[(.*)\]',line).group(1).split(', ')
  assert set(axioms)<={'propext','Classical.choice','Quot.sound'},line
 if module.startswith('R1Z.'):
  names=re.findall(r'^theorem (\w+)',p.read_text(),re.M)
  for name in names: assert any("."+name+"' depends on axioms:" in s for s in lines),(module,name)
 assert not re.search(r'\b(sorry|admit|native_decide)\b',p.read_text()),module
 checks.append(dict(module=module,attempt=attempt,source_sha256=sha,print_axioms=lines))
source=json.loads((E/'frozen-source-inventory.json').read_text())
for name,want in source['pins'].items():
 p=Path(name);assert hashlib.sha256(p.read_bytes()).hexdigest()==want['sha256'],name
frozen=json.loads((E/'pins/frozen-elf-final-check.json').read_text())
assert all(v['byte_identical'] and v['cmp_exit']==0 and v['receipt']['exit_status']==0 for v in frozen['programs'].values())
endpoint=json.loads((E/'endpoint/identity.json').read_text())
assert hashlib.sha256(Path(endpoint['path']).read_bytes()).hexdigest()==endpoint['sha256']
assert (E/'endpoint/deletion.diff').read_bytes()==b''
(E/'final-proof-audit.json').write_text(json.dumps(dict(checked_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),accepted_sources=checks,shipped_inputs_checked=len(source['pins']),endpoint_premises_deleted=0,full_manifest_replayed=False,scope='Focused source/helper evidence only; no native publication owner or whole-run refinement is claimed'),indent=2)+'\n')
print('Final proof bytes and axioms match accepted focused receipts; frozen sources match.')
