from pathlib import Path
import hashlib, json, re, subprocess, sys
root = Path(__file__).resolve().parent
repo = root.parents[4]
research = repo / 'docs/research/100bit-spend-path-20261013'
manifest = json.loads((root / 'manifest.json').read_text())
assert manifest['schema'] == 'focused-extractor-proof-packet-v1'
source_entry = manifest['modules'][0]
source = root / source_entry['source']
sha = lambda b: hashlib.sha256(b).hexdigest()
assert sha(source.read_bytes()) == source_entry['source_sha256']
imports = re.findall(r'^import\s+([\w.]+)\s*$', source.read_text(), re.M)
assert set(imports) == set(manifest['direct_import_source_map']), (imports, list(manifest['direct_import_source_map']))
for name, pin in manifest['direct_import_source_map'].items():
    imported = research / pin['source_path']
    assert imported.is_file(), (name, imported)
    assert sha(imported.read_bytes()) == pin['source_sha256'], name
check = manifest['source_body_checker']
generated = root / check['generated_source']
adapter = root / check['adapter_source']
assert sha(generated.read_bytes()) == check['generated_sha256']
assert sha(adapter.read_bytes()) == check['adapter_sha256']
res = subprocess.check_output([sys.executable, str(root / check['script']), str(generated), str(adapter)], text=True)
assert json.loads(res)['ok']
assert sha((root / check['result']).read_bytes()) == check['result_sha256']
assert not list(root.rglob('*.olean')) and not list(root.rglob('*.ilean'))
print('S4 installed three-push packet checks: PASS')
