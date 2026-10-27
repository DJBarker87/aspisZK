"""Validate retained evidence bindings; does not rerun native gates."""
from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1]
def read(p):return json.loads((E/p).read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
patch=E/'patches/0001-private-key-raw-fd.patch';cleanup=read('host/cleanup.json')
assert sha(patch)==cleanup['patch']['sha256']
assert patch.stat().st_size==4951
for p,h in read('source-pins.json')['files'].items():assert sha(R/p)==h,p
for p,h in read('build-inputs.json')['files'].items():assert sha(R/p)==h,p
assert read('host/source-comparison.json')['patched_changes']==['scripts/r1_devnet_spend.py','tools/r1-cost-probe/src/bin/devnet_spend.rs']
for row in read('host/fixtures.json')['rows']:
 assert sha(E/'fixtures'/f"request-{row['note']}.json")==row['request_sha256']
 assert all(v['byte_identical'] for v in row['files'].values())
 for n in ['base','patched']:
  assert 'N7_FIXTURE_ENTROPY_64' in (E/'host'/f"{n}-{row['note']}-stderr.log").read_text()
assert read('host/signing-fixture.json')['byte_identical']
assert all(r['matches'] and r['sha256']==r['expected'] for r in read('host/elf-pins.json')['rows'])
d=read('host/decoder.json');assert d['binary']['sha256']==cleanup['patched_binary']['sha256']
assert len(d['instructions'])==10 # nine executed instructions plus trailing INT3 padding
assert [r['instruction'].split()[0] for r in d['instructions']]==['movups']*8+['ret','int3']
s=read('resource-summary.json');assert len(s['rows'])==6
for r in s['rows']:
 assert r['cgroup_swap_peak_bytes']==r['process_swaps']==0
 assert list(r['limits'].values())==['6442450944','8589934592','0','64']
 assert r['exit_status']==(1 if r['name']=='build-base' else 0)
assert cleanup['cargo_target_removed'] and cleanup['elf_pins_rechecked']
assert cleanup['Lean_attempts']==cleanup['Kani_attempts']==0
changed=subprocess.check_output(['git','diff','--name-only','0c9dc9a4cc'],cwd=R,text=True).splitlines()
assert all(p.startswith(('evidence/pv-n7-20261027/','design/PV-N7-20261027.md')) for p in changed)
subprocess.run(['git','apply','--check',str(patch)],cwd=R,check=True)
# A unified patch needs a literal space for blank context lines. Preserve its
# pinned bytes and check it by git apply; check whitespace on all other files.
subprocess.run(['git','diff','--check','0c9dc9a4cc','--','.',
                ':(exclude)evidence/pv-n7-20261027/patches/0001-private-key-raw-fd.patch'],cwd=R,check=True)
print('PASS: source unchanged, patch applicable, binary/fixture/ELF/receipt/cleanup bindings, path limits')
