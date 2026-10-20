#!/usr/bin/env python3
"""Reconstruct and hash-check each historical dependency-free tool input.
No proof is rerun. A content-addressed snapshot covers every Kani receipt.
"""
import hashlib,json,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'docs/research/100bit-spend-path-20261013/evidence/r22-overflow-20261021'
PREFIX='tools/r22-overflow-kit/generated/'
def sha(b):return hashlib.sha256(b).hexdigest()
def old(rev):
    names=subprocess.check_output(['git','ls-tree','--name-only',rev+':'+PREFIX.rstrip('/')],cwd=ROOT,text=True).splitlines()
    return {n:subprocess.check_output(['git','show',rev+':'+PREFIX+n],cwd=ROOT) for n in names}
def repin(files):
    pin=json.loads(files['source-pins.json']);pin['generated']={k:sha(v) for k,v in files.items() if k!='source-pins.json'}
    files['source-pins.json']=(json.dumps(pin,indent=2,sort_keys=True)+'\n').encode();return files
sets=[old('d38080918'),old('4c67f1650')]
predev=dict(sets[0]);predev['Cargo.toml']=predev['Cargo.toml'].replace(b'[profile.dev]\noverflow-checks=true\nopt-level=3\ndebug=false\n',b'');sets.append(repin(predev))
finite=dict(sets[1]);finite['multiproof.rs']=finite['multiproof.rs'].replace(b'#[cfg(kani)] #[kani::proof]\nfn dedup_step_all_positions()',b'#[cfg(kani)] #[kani::proof] #[kani::unwind(34)]\nfn dedup_step_all_positions()')
finite['layout.rs']=finite['layout.rs'].replace(b'#[kani::unwind(20)]\nfn batch_key_ranges()',b'#[kani::unwind(24)]\nfn batch_key_ranges()').replace(b'fn checkpoint_reader_32() {reader_case::<32>();}',b'''fn checkpoint_reader_32() {
    let bytes=[0u8;4880];let at:usize=kani::any();kani::assume(at<=4880-32);
    let mut r=Reader{bytes:&bytes,at};let _out=r.raw::<32>();
    assert_eq!(r.at,at+32);
}''');sets.append(repin(finite))
sets.append(old('a976feb5e'))
sets.append({p.name:p.read_bytes() for p in (ROOT/PREFIX).iterdir() if p.suffix in ['.rs','.toml','.json']})
byfp={sha(s['source-pins.json']):s for s in sets};rows=[]
for receipt in sorted((OUT/'kani').glob('*/receipt.json')):
    rec=json.loads(receipt.read_text());fp=rec['deps_fingerprint'];assert fp in byfp,('missing exact pins',receipt,fp)
    files=byfp[fp]
    for n,h in rec['inputs'].items():assert sha(files[n])==h,(receipt,n)
    dst=OUT/'source-snapshots'/fp
    dst.mkdir(parents=True,exist_ok=True)
    for n,b in files.items():(dst/n).write_bytes(b)
    rows.append(dict(attempt=rec['attempt'],deps_fingerprint=fp,source_snapshot=str(dst.relative_to(OUT)),inputs_match=True))
(OUT/'source-snapshot-index.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps({'attempts_bound_to_exact_sources':len(rows),'unique_snapshots':len({r['deps_fingerprint'] for r in rows})}))
