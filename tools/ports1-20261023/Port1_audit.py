#!/usr/bin/env python3
"""Source-only preflight and final focused receipts, no compiler/solver launch."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2]; E=R/'evidence/ports1-20261023'; L=R/'docs/research/100bit-spend-path-20261013/lean'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def body(s,needle):
 a=s.index(needle); b=s.index('{',a); n=1; i=b+1
 while n:
  n+=(s[i]=='{')-(s[i]=='}'); i+=1
 return s[a:i]
wide=R/'crates/aspis-core/src/field/wide_exact.rs'
retained=R/'tools/wide-parser-unrolled-candidate/field/wide_exact.rs'
for needle in ['pub fn from_le_bytes(', 'pub fn from_limbs(']:
 assert body(wide.read_text(),needle)==body(retained.read_text(),needle),needle
# Verify that the installed Lean decoder is exactly the retained generated
# body after the stated identifier-only relocation (no resource options).
s=(L/'UnrolledWideParserSource.lean').read_text();a=s.index('def field.wide_exact.WideExact.from_limbs_unrolled'); b=s.index('/-- [aspis_core::parse_wide_exact_probe]')
s=s[a:b].replace('field.wide_exact.WideExact.from_limbs_unrolled','fromLimbs').replace('field.wide_exact.WideExact.from_le_bytes_unrolled','decode').replace('field.wide_exact.WideExact.BYTE_LEN','32#usize').replace('field.wide_exact.WideExact','aspis_core.field.wide_exact.WideExact').replace('field.P','2147483647#u32')
assert s in (L/'Port1_LibrarySource.lean').read_text()
# Closed arithmetic on the Rust const expressions, not cargo evaluation.
semantic=12903+29*32
values={'HEADER':16,'LOGICAL_SEMANTIC':semantic,'SEMANTIC_COMPACT_VALUES':1+10*28+(87+29)+29,'COMPACT_Y1':29*16,'SPLIT':10,'FINAL_LEN':64}
values['COMPACT_SEMANTIC']=semantic-16*values['SEMANTIC_COMPACT_VALUES']
values['OFF_SEMANTIC']=16
for name,previous,delta in [('OFF_Y1','OFF_SEMANTIC',values['COMPACT_SEMANTIC']),('OFF_INACTIVE','OFF_Y1',464),('OFF_ROUND0','OFF_INACTIVE',32),('OFF_FOLDED_ROOT','OFF_ROUND0',224),('OFF_ROUND1','OFF_FOLDED_ROOT',32),('OFF_FINAL','OFF_ROUND1',224),('OFF_OPENINGS','OFF_FINAL',64*32)]:values[name]=values[previous]+delta
expected={14:('OFF_ROUND1',7783),15:('OFF_FOLDED_ROOT',7751),16:('SPLIT',10),20:('OFF_OPENINGS',10055),21:('OFF_FINAL',8007),22:('OFF_ROUND0',7527),23:('OFF_INACTIVE',7495)}
install=(L/'Port1_Library.lean').read_text()
for op,(name,value) in expected.items():
 assert values[name]==value
 assert f'op{op} := .ok {value}#usize' in install
# Pin exact source declarations used for the arithmetic and no-read inspection.
compact=R/'crates/aspis-r1-cost-probe/src/compact.rs'
for text in ['pub const SPLIT: usize = 10;','pub const HEADER: usize = 16;','pub const OFF_Y1: usize = OFF_SEMANTIC + COMPACT_SEMANTIC;','pub const OFF_INACTIVE: usize = OFF_Y1 + COMPACT_Y1;','pub const OFF_ROUND0: usize = OFF_INACTIVE + 32;','pub const OFF_FOLDED_ROOT: usize = OFF_ROUND0 + 224;','pub const OFF_ROUND1: usize = OFF_FOLDED_ROOT + 32;','pub const OFF_FINAL: usize = OFF_ROUND1 + 224;','pub const OFF_OPENINGS: usize = OFF_FINAL + FINAL_LEN * 32;']:
 assert text in compact.read_text(),text
assert 'fn mark(obs:Observer,p:Phase) { if let Some(f)=obs {f(p);} }' in (R/'crates/aspis-r1-cost-probe/src/verifier.rs').read_text()
assert 'pub const ZERO: Self = Self {' in wide.read_text()
paths=[wide,retained,compact,R/'crates/aspis-r1-cost-probe/src/verifier.rs',R/'crates/aspis-r1-cost-probe/src/candidate.rs',L/'UnrolledWideParserSource.lean',R/'evidence/verifier-top-20261023/generated-complete/adaptation.json']
source_pins={str(p.relative_to(R)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in paths}
accepted={};attempts=[]
for p in sorted(E.glob('lean-*/receipt.json')):
 x=json.loads(p.read_text()); attempts.append({'attempt':x['attempt'],'exit_status':x['exit_status'],'receipt':str(p.relative_to(R))})
 if x['exit_status']!=0: continue
 for f,h in x['source_hashes'].items():
  if (L/f).exists() and sha(L/f)==h:
   assert all('sorryAx' not in a and 'axiom' in a for a in x['print_axioms'])
   accepted[f]=str(p.relative_to(R))
for p in L.glob('Port1_*.lean'):
 assert p.name in accepted, f'No final-source accepted receipt: {p.name}'
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option (maxRecDepth|maxHeartbeats)',p.read_text())
manifest={'schema':'focused-extractor-proof-packet-v1','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'source_pins':source_pins,'constant_values':values,'accepted_final_modules':accepted,'attempts':attempts,'compiler_free_preflights':['lean-002'],'lean_compiles':len(attempts),'kani_runs':0,'release_replay':False,'source_artifact_binding':'Source identities and inherited extraction only; no new ELF claim'}
(E/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n'); print(json.dumps({'accepted_final_modules':accepted,'lean_compiles':len(attempts),'kani_runs':0}))
