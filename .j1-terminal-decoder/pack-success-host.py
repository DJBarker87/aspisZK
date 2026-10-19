from pathlib import Path
import hashlib, json, tarfile, io
root=Path('/home/dombarker/project-offloads/aspis-r1-j1a-terminal-decoder-copy-helper-proof-20261016')
w=root/'proofs'
names=['AspisR1TerminalDecoder.Types','AspisR1TerminalDecoder.FunsExternal','AspisR1TerminalDecoder.Funs','ExtractedTerminalDecoderSuccess']
files={}
def add(p):
    assert p.is_file() and not p.is_symlink(),p
    files[str(p.relative_to(root))]=p
for n in names:
    rel=n.replace('.','/')
    add(w/'sources'/f'{rel}.lean')
    rp=w/'successful-targets'/f'{n}.json'; add(rp)
    receipt=json.loads(rp.read_text())
    for obj in receipt['objects'].values(): add(Path(obj['path']))
for p in [w/'sources/SOURCE-MANIFEST.json',w/'runner.py',w/'history/SOURCE-MANIFEST-before-success.json',w/'history/success-reservation-a.json']: add(p)
for attempt in ['success-a','success-b','success-c','success-d']:
    for p in (w/'runs'/attempt).rglob('*'):
        if p.is_file() and not p.is_symlink(): add(p)
hashes={n:hashlib.sha256(p.read_bytes()).hexdigest() for n,p in sorted(files.items())}
out=root/'decoder-success.tar.gz'
with tarfile.open(out,'w:gz') as t:
    seen={}
    for n,p in sorted(files.items()):
        h=hashes[n]
        if h in seen:
            info=tarfile.TarInfo(n);info.type=tarfile.LNKTYPE;info.linkname=seen[h];t.addfile(info)
        else:
            t.add(p,arcname=n,recursive=False);seen[h]=n
    data=''.join(h+'  '+n+'\n' for n,h in hashes.items()).encode()
    info=tarfile.TarInfo('SHA256SUMS');info.size=len(data);t.addfile(info,io.BytesIO(data))
manifest={
 'format':1,'archive':out.name,'archive_sha256':hashlib.sha256(out.read_bytes()).hexdigest(),
 'archive_bytes':out.stat().st_size,'archive_entries':len(files)+1,
 'proof_base_revision':'b2ad6649de4c1b97c2270a1c8bd4bbfe5537d52c',
 'rust_source_revision':'0626294e34632812accf4cb14704f027368ea871',
 'generated_cone_evidence':'../terminal-decoder-432-20261016/manifest.json',
 'target':'ExtractedTerminalDecoderSuccess',
 'modules':{n:json.loads((w/'successful-targets'/f'{n}.json').read_text()) for n in names},
 'attempts':{a:json.loads((w/'runs'/a/'ExtractedTerminalDecoderSuccess/receipt.json').read_text()) for a in ['success-a','success-b','success-c','success-d']},
 'scope':'Actual emitted outer decoder success implies same returned object validator success and same-input length/header read/comparison witnesses. No deep decoder inversion/serializer roundtrip, Rust/runtime preservation, custody, or account authentication theorem.',
 'external_snapshot_sha256':hashlib.sha256((w/'runs/success-d/external-inputs.json').read_bytes()).hexdigest(),
 'runner_sha256':hashlib.sha256((w/'runner.py').read_bytes()).hexdigest()
}
(root/'decoder-success-manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:manifest[k] for k in ['archive','archive_sha256','archive_bytes','archive_entries','external_snapshot_sha256','runner_sha256']},indent=2))
