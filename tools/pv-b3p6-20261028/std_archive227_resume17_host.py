from pathlib import Path
import urllib.request,json,hashlib,tomllib,tarfile
H=Path('/home/dombarker/project-offloads/codex-pv-b3p6-20261028');R=H/'resume17';O=R/'std-sources'
url='https://static.rust-lang.org/dist/2025-11-21/channel-rust-nightly.toml';raw=urllib.request.urlopen(url,timeout=30).read();manifest=tomllib.loads(raw.decode());entry=manifest['pkg']['rust-src']['target']['*'];u=entry['xz_url'];expected=entry['xz_hash']
archive=O/'rust-src-nightly.tar.xz'
if not archive.exists():archive.write_bytes(urllib.request.urlopen(u,timeout=60).read())
assert hashlib.sha256(archive.read_bytes()).hexdigest()==expected
reached=json.loads((R/'std-reached.json').read_text());matches=[]
with tarfile.open(archive,'r:xz')as t:
 members={m.name.split('/lib/rustlib/src/rust/library/',1)[1]:m for m in t if '/lib/rustlib/src/rust/library/'in m.name and m.isfile()}
 for rel,record in reached['files'].items():
  if 'error'in record:continue
  data=t.extractfile(members[rel]).read();actual=hashlib.sha256(data).hexdigest();assert actual==record['kani_source_sha256'],(rel,actual,record['kani_source_sha256'])
  matches.append(dict(file=rel,sha256=actual,official_component_matches_recovered_source=True))
(R/'std-source-authority.json').write_text(json.dumps(dict(manifest_url=url,manifest_sha256=hashlib.sha256(raw).hexdigest(),component_url=u,component_sha256=expected,component_bytes=archive.stat().st_size,source_files=matches,no_install_or_sysroot_modification=True),indent=2)+'\n')
print('official rust-src component matches',len(matches),'reached files')
