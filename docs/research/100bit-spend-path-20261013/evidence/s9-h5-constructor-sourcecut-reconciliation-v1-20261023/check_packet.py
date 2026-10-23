from pathlib import Path
import json,hashlib
r=Path(__file__).resolve().parent;m=json.loads((r/'manifest.json').read_text())
for f in m['files']:
 p=r/f['path'];assert hashlib.sha256(p.read_bytes()).hexdigest()==f['sha256'] and p.stat().st_size==f['bytes']
def ext(s,marker):
 i=s.index(marker);a=s.index('{',i);d=1;j=a+1
 while d:d+=(s[j]=='{')-(s[j]=='}');j+=1
 return s[i:j]
ids=json.loads((r/'retained-attempt22/source-identities.json').read_text())['files']
for rel in ['field.rs','field/wide_exact.rs','circle.rs']:assert hashlib.sha256((r/'sources/crates/aspis-core/src'/rel).read_bytes()).hexdigest()==ids['input/src/'+rel]
w=(r/'sources/crates/aspis-r1-cost-probe/src/weights.rs').read_text();lib=(r/'retained-attempt22/input/src/lib.rs').read_text();norm=lambda s:''.join(s.split())
for marker in ['pub fn new(variant:Variant','fn box_from_parts(']:assert '#[inline(never)]' in w[max(0,w.index(marker)-32):w.index(marker)]
for marker in ['fn box_from_parts(']:assert norm(ext(w,marker))==norm(ext(lib,marker))
a=ext(w,'pub fn new(variant:Variant');a=a[a.index('{')+1:-1].replace('Self::box_from_parts','Weights::box_from_parts');b=ext(lib,'pub fn weights_new(');assert norm(a)==norm(b[b.index('{')+1:-1])
assert ext((r/'sources/state_only_prefix.explicit.rs').read_text(),'fn state_only_statement_points(')==ext((r/'retained-attempt22/input/src/state_only_prefix.rs').read_text(),'fn state_only_statement_points(')
for p in r.rglob('*'):
 if p.is_file():assert p.suffix not in {'.so','.elf','.bin','.olean','.ilean','.ir','.llbc','.dylib','.dll'}
print('PASS: H5+explicitCore source spans match attempt22attrs; standard Box erasure identified, runtime trust remains explicit')
