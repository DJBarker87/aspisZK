from pathlib import Path
import difflib, hashlib, json, shutil, subprocess

old = Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016')
new = Path('/home/dombarker/project-offloads/aspis-r1-aeneas-geometry-20261016')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert not new.exists()
new.mkdir()
shutil.copytree(old / 'aeneas', new / 'aeneas', symlinks=True)
original = (old / 'aeneas/src/Translate.ml').read_text()
before = '  Format.pp_set_margin fmt 80;'
after = '  Format.pp_set_geometry fmt ~max_indent:1000 ~margin:1024;'
assert original.count(before) == 1
changed = original.replace(before, after)
(new / 'aeneas/src/Translate.ml').write_text(changed)
(new / 'geometry.patch').write_text(''.join(difflib.unified_diff(original.splitlines(True), changed.splitlines(True), fromfile='aeneas/src/Translate.ml', tofile='aeneas/src/Translate.ml')))
pins = {}
for p in sorted((old / 'aeneas').rglob('*')):
    if '_build' in p.parts or not p.is_file() or p.is_symlink():
        continue
    rel = p.relative_to(old)
    q = new / rel
    if rel != Path('aeneas/src/Translate.ml'):
        assert p.read_bytes() == q.read_bytes(), rel
    pins[str(rel)] = {'before': sha(p), 'after': sha(q)}
(new / 'source-change.json').write_text(json.dumps({'base_revision': 'b59d5188c082f704a418c7cb4e52ad69328002d1', 'only_source_change': 'aeneas/src/Translate.ml:1421', 'generated_version_label': 'b59d5188c082f704a418c7cb4e52ad69328002d1-geometry1024', 'files': pins}, indent=2) + '\n')
(new / 'inputs').mkdir()
shutil.copy2(old / 'inputs/source-archives.json', new / 'inputs/source-archives.json')
shutil.copy2(Path(__file__).with_name('build-aeneas-geometry.sh'), new / 'build-aeneas.sh')
runner = (old / 'run-aeneas-container.py').read_text()
runner = runner.replace(str(old), str(new)).replace("name='aspis-r18-tools-20261016-a'", "name='aspis-r1-aeneas-geometry-20261016-a'")
(new / 'run-aeneas-container.py').write_text(runner)
cmd = ['docker', 'create', '--name', 'aspis-r1-aeneas-geometry-20261016-a', '--network', 'none', '--read-only', '--memory', '8g', '--memory-swap', '8g', '--tmpfs', '/tmp:rw,size=512m', '--mount', 'type=bind,src=' + str(new) + ',dst=/work', '--mount', 'type=bind,src=' + str(old / 'charon') + ',dst=/work/charon,readonly', 'sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7', 'bash', '/work/build-aeneas.sh']
subprocess.run(cmd, check=True)
print('Verified source files:', len(pins), 'one formatting change; private container created but not started', flush=True)
