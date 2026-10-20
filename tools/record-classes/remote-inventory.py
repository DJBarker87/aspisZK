"""Read-only environment resolution supplement for launcher fingerprints."""
import hashlib, json, pathlib, re
J = pathlib.Path('/home/dombarker/project-offloads/aspis-joint-20261019')
H = pathlib.Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019')
env = json.loads((H / 'env/J.json').read_text())
paths = [J / 'objects'] + [pathlib.Path(p) for p in env['LEAN_PATH'].split(':')]
def pin(p):
    return {'path': str(p), 'sha256': hashlib.sha256(p.read_bytes()).hexdigest(),
            'size_bytes': p.stat().st_size}
mods = ['WireBindingRecordCodec', 'R1Z.WireBindingLengthsR1PBin', 'R1Z.WireLengthsR1PBin',
        'R1Z.FinalR1PBin', 'R1Z.PrivacyR1PBin', 'R1Z.PrivacyBoundR1PBin', 'R1J.PrivacySamplerSpendBin']
items = []
for m in mods:
    src = J / 'sources' / (m.replace('.', '/') + '.lean')
    deps = []
    for imp in re.findall(r'^import (\S+)', src.read_text(), re.M):
        found = next((p / (imp.replace('.', '/') + '.olean') for p in paths
                      if (p / (imp.replace('.', '/') + '.olean')).exists()), None)
        assert found is not None, imp
        deps.append({'module': imp, **pin(found)})
    items.append({'module': m, 'source': pin(src),
                  'object': pin(J / 'objects' / (m.replace('.', '/') + '.olean')),
                  'resolved_imports': deps})
print(json.dumps({'env': 'J', 'lean_path': env['LEAN_PATH'], 'modules': items,
                  'note': 'Read-only post-build supplement. Launcher fingerprints retain their original J-object-only algorithm; package/core imports resolve here.'}, indent=2))
