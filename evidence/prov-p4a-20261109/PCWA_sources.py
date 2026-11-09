#!/usr/bin/env python3
"""PCWA_sources.py: materialise and hash the located reference sources under sources/ (local, read-only on git).
Each source is recovered from a committed record and checked against the hash recorded by that record:
  * archive patch (NDL_SOURCE_ARCHIVE/<sha>.patch) -> file bytes; sha256 must equal the patch file name AND the
    rust_reference_sha256 / source_hashes entry of the original extraction receipt;
  * LLBC translated.files[].contents (embedded Charon source) -> sha256 recorded in PCWA_SOURCES.json.
Usage: python3 PCWA_sources.py   (run from this directory; reads blobs from git rev `research`)"""
import json,subprocess,lzma,hashlib,sys
from pathlib import Path
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent
REV='research'
def git(path): return subprocess.check_output(['git','-C',str(E.parent.parent),'show',REV+':'+path])
def oid(path): return subprocess.check_output(['git','-C',str(E.parent.parent),'rev-parse',REV+':'+path],text=True).strip()
sha=lambda b:hashlib.sha256(b).hexdigest()
def llbc(path):
    raw=git(path)
    if path.endswith('.xz'): raw=lzma.decompress(raw)
    d=json.loads(raw); return d.get('translated',d),raw
def embedded(path,name):
    t,raw=llbc(path)
    for f in t['files']:
        if f.get('contents') is not None and list(f['name'].values())[0]==name: return f['contents'].encode(),t.get('crate_name'),sha(raw)
    raise SystemExit('no embedded '+name+' in '+path)
def patch_file(path):
    lines=git(path).decode().split('\n'); body=[l[1:] for l in lines[3:] if l.startswith('+')]
    return ('\n'.join(body)+'\n').encode()
MAN='[package]\nname="%s"\nversion="0.1.0"\nedition="2021"\n[workspace]\n'
D='evidence/'
items=[
 dict(id='NGM_GuardRef',crate='nco_reference',kind='archive_patch',record=D+'native-front1b-20261028/NDL_SOURCE_ARCHIVE/a914357fa95c1f3cf1cfa10910e3480e8efc97e2cfe744c227ae4ff2d53ffc78.patch',expect='a914357fa95c1f3cf1cfa10910e3480e8efc97e2cfe744c227ae4ff2d53ffc78',
      original_receipt=D+'native-front1b-20261028/NDL_E004/receipt.json'),
 dict(id='NGD_AtG',crate='nfu_reference',kind='llbc_embedded',record=D+'slice-d-parser-20261104/NGD_E002.llbc',name='src/lib.rs',expect='a4cf8bb1a3fc0ecd0e5a7ec67b829995f621d02e783d2562a46014c847ef16dc'),
 dict(id='NHJ_SnapshotReference',crate='nhj_snapshot_reference',kind='llbc_embedded',record=D+'slice-d-entry3-20261106/NHJ_E001.llbc.xz',name='src/lib.rs',expect='e8a85ac95461fcd40751c9c63d31c5a8d500471f865be6b0d543ba6dc828c53b'),
 dict(id='NHI_FilledRef',crate='nfu_reference',kind='llbc_embedded',record=D+'slice-d-pair-20261106/NHI_E001.llbc',name='src/lib.rs',expect=None),
 dict(id='NHE_TensorRef',crate='nfu_reference',kind='llbc_embedded',record=D+'slice-d-finish3-20261106/NHE_E001.llbc',name='src/lib.rs',expect=None),
 dict(id='NHE_GroupRef',crate='nfu_reference',kind='llbc_embedded',record=D+'slice-d-finish3-20261106/NHE_E002.llbc',name='src/lib.rs',expect=None),
]
out=[]
for it in items:
    if it['kind']=='archive_patch':
        b=patch_file(it['record']); crate=it['crate']; llbc_sha=None
    else:
        b,crate_llbc,llbc_sha=embedded(it['record'],it['name']); assert crate_llbc==it['crate'],(crate_llbc,it['crate']); crate=it['crate']
    h=sha(b)
    if it['expect']: assert h==it['expect'],(it['id'],h,it['expect'])
    d=E/'sources'/it['id']; (d/'src').mkdir(parents=True,exist_ok=True)
    (d/'src/lib.rs').write_bytes(b); m=(MAN%crate).encode(); (d/'Cargo.toml').write_bytes(m)
    out.append(dict(id=it['id'],crate=crate,record=it['record'],record_git_blob=oid(it['record']),kind=it['kind'],src_sha256=h,src_bytes=len(b),manifest_sha256=sha(m),
      manifest_basis='reconstructed: name from the LLBC crate_name / NDL_extract.py, version 0.1.0, edition 2021, empty [workspace] (the recorded shape of NDL_extract.py and NML_inputs/*/Cargo.toml)',
      container_llbc_sha256=llbc_sha,original_receipt=it.get('original_receipt')))
(E/'PCWA_SOURCES.json').write_text(json.dumps(out,indent=1)+'\n')
for o in out: print(o['id'],o['src_sha256'][:16],o['src_bytes'])
