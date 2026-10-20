#!/usr/bin/env python3
"""Portable exact-source/cut checker for the Query31 axiom-free owners."""
from pathlib import Path
from hashlib import sha256
import re, sys, json

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / 'sources'
SNAP = ROOT / 'source-snapshot'
GEN = SNAP / 'generated/AspisR1Query31Transcript'
EXPECTED = {
    'generated_funs': 'd192f7291571583454e7758fabcfde32f7f6df965e4bd9e4d90a0bf76b67d9c5',
    'generated_types': '06da263a656a32ea7c3e5290a12776108a70dbc3428a2bfaf3e7378949d7c5f5',
    'generated_funs_external_template': 'f74ee4f56905513f3c990808fc427fed1d29f5f043f60106a33a342ccce01021',
    'firststop_v14': 'ea5c3cb0449e09d7c12f8b98adf7fbc2be19137ca4f64f6122bc879689a7597b',
    'scan_body': '5c06d838975254a98556e2d0d3164b202cbcf3cb3996dc0244cd7c3150bfe533',
    'minimal_types': 'b0a086e9bcd8c0b1d2131b0796711fddf98df75b44d6c4a3a10d9aca51e9e07d',
    'q22_source': 'cee29f654f30ebb9d6ee5f422fc6f9f7d2c031d803d0deafff0f59252e150b58',
    'sampler_words_source': '21f5742355920ce7f6a70496e6255e8d50d10739a75b8a5671030eea6fb1dbb9',
    'rust_r0': '2a315219d20069742c7c07e2a1ab8ee283865be3c607fdde2cf6975ad1813fc1',
    'rust_transcript': '9bd74c66a28567e4d964896b7e2d7c0ac79840565d44b561747879868bdd9179',
    'rust_std_array_iter': '570b98951edb1bf47932c2de58dc4d3f38f34d37b3dffeac2fe80572dc0475cb',
    'rust_std_iter_inner': '6906e8e1e1956d415a9058df036e2a28fe0938dbae0b2c499a5889d8b983c4c1',
    'rust_std_index_range': 'be7f1a663156319aa4762288c44b726338276f0bcb1c36a5ced5003d329deb8f',
    'rust_std_maybe_uninit': 'cd1152779de3a6bc96b29997e8a95d3beb9ff1018f99223b429ed0df66baa8ef',
}

def digest(p): return sha256(p.read_bytes()).hexdigest()
def require_hash(name,p):
    actual=digest(p)
    if actual != EXPECTED[name]: raise SystemExit(f'{name} hash mismatch: {actual}')
    return actual

def source_decl(text,name):
    m=re.search(r'(?m)^def\s+'+re.escape(name)+r'(?=\s|:|\n)',text)
    if not m: raise ValueError('missing '+name)
    ds=[m.end()+q.start() for q in re.finditer(r'(?m)^(?:private\s+)?(?:def|theorem|lemma)\s',text[m.end():])]
    e=min([x for x in [text.find('\n/--',m.end()),*ds] if x>=0],default=len(text))
    return text[m.start():e]

def compact(s):
    s=re.sub(r'(?m)^\s*--.*$','',s)
    s=re.sub(r'/\-.*?\-/','',s,flags=re.S)
    return re.sub(r'\s+',' ',s).strip()

funs=GEN/'Funs.lean'; types=GEN/'Types.lean'; ext=GEN/'FunsExternal_Template.lean'
first=SRC/'Query31UnrolledDriverFirstStop.lean'; first_raw=SNAP/'Query31UnrolledDriverFirstStop-v14.lean'
body=SRC/'Query31ExplicitScanBody.lean'; min_types=SRC/'Query31ScanTypesOnly.lean'
for name,p in [('generated_funs',funs),('generated_types',types),('generated_funs_external_template',ext),('firststop_v14',first_raw),('scan_body',body),('minimal_types',min_types)]: require_hash(name,p)
# The accepted first-stop file differs from checked v14 only by replacing its
# broad generated Types import with the axiom-free minimal owner.
adapted=first.read_text().replace('import Query31ScanTypesOnly','import AspisR1Query31Transcript.Types',1)
if adapted != first_raw.read_text(): raise SystemExit('first-stop source differs beyond minimal-owner import')
# Pin exact copied constants and finish, plus entire copied driver, via whole-file equality above.
raw=funs.read_text(); cut=body.read_text()
scan_decl=source_decl(raw,'aspis_core.r0_transcript.QueryScan.scan_loop.body')
raw_body=scan_decl.split(':= do',1)[1].strip()
ours=source_decl(cut,'body').split(':= do',1)[1].strip()
repls=[
 (r'core\.array\.iter\.IntoIter\.Insts\.CoreIterTraitsIteratorIterator\.next iter','ops.iterNext iter'),
 (r'let s ←\s*core\.array\.Array\.index.*?self\.accepted \{ «end» := self\.accepted_len \}','let sl ← ops.readPrefix s.accepted s.accepted_len'),
 (r'core\.slice\.Slice\.contains core\.cmp\.PartialEqU32 s candidate','ops.contains sl candidate'),
 (r'Array\.update self\.accepted self\.accepted_len candidate','ops.update s.accepted s.accepted_len candidate'),
 (r'self\.draws \+ 1#usize','ops.usizeAdd s.draws 1#usize'),
 (r'self\.accepted_len \+ 1#usize','ops.usizeAdd s.accepted_len 1#usize'),
 (r'aspis_core\.r0_transcript\.QUERY_COUNT','22#usize'),
 (r'aspis_core\.r0_transcript\.QUERY_MAX_DRAWS','64#usize'),
 (r'\bdone\b','ControlFlow.done'),(r'\bcont\b','ControlFlow.cont'),(r'\bself\b','s')]
for pat,repl in repls: raw_body=re.sub(pat,repl,raw_body,flags=re.S)
if compact(raw_body)!=compact(ours): raise SystemExit('scan body differs beyond explicit operation/constant/name cut')
# Exact QueryScan fields and QuerySampleError constructors used by the minimal owner.
t=types.read_text()
m=re.search(r'(?ms)^structure\s+aspis_core\.r0_transcript\.QueryScan\s+where\s*(.*?)(?=^end\s+AspisR1Query31Transcript)',t)
if not m: raise SystemExit('generated QueryScan source record missing')
fields=compact(m.group(1))
if fields != 'accepted : Array Std.U32 22#usize accepted_len : Std.Usize draws : Std.Usize': raise SystemExit('QueryScan fields differ: '+fields)
minimal=min_types.read_text()
for needle in ['| BoundNotPowerOfTwo : Std.U32','| CountExceedsBound : Std.Usize → Std.U32','| DrawLimitExhausted : Std.Usize → Std.Usize','accepted : Array Std.U32 22#usize','accepted_len : Std.Usize','draws : Std.Usize']:
    if needle not in minimal: raise SystemExit('minimal owner missing '+needle)
if 'axiom ' in minimal or 'FunsExternal' in minimal or 'TypesExternal' in minimal: raise SystemExit('axiomatic external owner imported/declared')
for p in SRC.glob('*.lean'):
    text=p.read_text()
    if 'import AspisR1Query31Transcript.Funs' in text or 'import AspisR1Query31Transcript.FunsExternal' in text or 'TypesExternal' in text:
        raise SystemExit(f'forbidden generated external import in {p.name}')
# Keep the raw FunsExternal template only as diagnostic evidence: these are the
# two unproved standard-library operations still used by the generated call graph.
if not re.search(r'axiom\s+Array\.Insts\.CoreIterTraitsCollectIntoIteratorTIntoIter\.into_iter',ext.read_text()):
    raise SystemExit('expected IntoIterator external declaration not found')
if not re.search(r'axiom\s+core\.array\.iter\.IntoIter\.Insts\.CoreIterTraitsIteratorIterator\.next',ext.read_text()):
    raise SystemExit('expected IntoIter::next external declaration not found')
# Pin the retained Q22 source and its direct source dependency.
q22=SNAP/'lean/AspisV8R19/Q22WordScan.lean'
sampler_words=SNAP/'lean/AspisV8R19/SamplerWords.lean'
require_hash('q22_source',q22)
require_hash('sampler_words_source',sampler_words)
if 'import AspisV8R19.SamplerWords' not in q22.read_text(): raise SystemExit('Q22 direct dependency changed')
# Verify source snapshot hashes for Rust and pinned Rust core files.
rustroot=SNAP/'rust'
for name,rel in [
 ('rust_r0','crates/aspis-core/src/r0_transcript.rs'),
 ('rust_transcript','crates/aspis-core/src/transcript.rs'),
 ('rust_std_array_iter','core/array/iter.rs'),
 ('rust_std_iter_inner','core/array/iter/iter_inner.rs'),
 ('rust_std_index_range','core/ops/index_range.rs'),
 ('rust_std_maybe_uninit','core/mem/maybe_uninit.rs')]:
    require_hash(name,rustroot/rel)
print(json.dumps({'pass':True,'generated_funs_sha256':EXPECTED['generated_funs'],'generated_types_sha256':EXPECTED['generated_types'],'firststop_source_relation':'exact except import AspisR1Query31Transcript.Types -> Query31ScanTypesOnly','scan_body_relation':'exact after explicit five Std op boundaries, source constants, and names','unproved_external_operations':['array IntoIterator::into_iter','array IntoIter::next'],'external_templates':'snapshot only; no accepted Lean source imports them','rust_source_hashes':{k:v for k,v in EXPECTED.items() if k.startswith('rust_')}},indent=2))
