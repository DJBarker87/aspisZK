#!/usr/bin/env python3
"""Compare the frozen parser cone with its retained extracted reference cut."""
from pathlib import Path
import re,json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s2-kani-20261021'
def item(s,m):
 a=s.index(m);b=s.index('{',a);d=1;e=b+1
 while d:d+=(s[e]=='{')-(s[e]=='}');e+=1
 return s[a:e]
def canon(s):return ''.join(re.sub(r'//[^\n]*','',s).split())
wire=R/'crates/aspis-r1-cost-probe/src/r1_wire.rs';wide=R/'crates/aspis-core/src/field/wide_exact.rs';field=R/'crates/aspis-core/src/field.rs';ref=R/'docs/research/100bit-spend-path-20261013/tools/prefix-aggregate-extraction-kit/lib.rs'
rows=[]
groups=[(wire,['pub const fn row_shape(','fn validate_record_fields(','pub fn parse_record(',"fn parse_record_at<'a>",'pub fn parse(bytes:','pub fn record(&self,','pub fn payload(&self,','pub(crate) fn validated_record(&self,','pub struct Prefix<','pub(crate) struct ValidatedRecord<']), (wide,['pub struct WideExact {','pub const fn c1(','pub fn from_limbs(','pub fn from_le_bytes(']),(field,['pub struct M31(','pub struct CM31 {','pub struct QM31 {'])]
for p,markers in groups:
 assert subprocess.check_output(['git','show','b2727acd3:'+str(p.relative_to(R))])==p.read_bytes()
 for marker in markers:
  # Tuple structs have no body; compare their declaration directly.
  if marker=='pub struct M31(':
   a=re.search(r'pub struct M31\([^;]+;',p.read_text())[0];b=re.search(r'pub struct M31\([^;]+;',ref.read_text())[0]
  else:a=item(p.read_text(),marker);b=item(ref.read_text(),marker)
  assert canon(a)==canon(b),marker
  rows.append(dict(source=str(p.relative_to(R)),marker=marker,source_declaration_sha256=hashlib.sha256(a.encode()).hexdigest(),reference_declaration_sha256=hashlib.sha256(b.encode()).hexdigest(),normalized_equal=True))
result=dict(schema='s2-retained-parser-binding-v1',revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),sources={str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [wire,wide,field,ref]},declarations=rows,reference_pins=str(ref.with_name('source-pins.json').relative_to(R)),qualification='Declaration identity modulo whitespace/comments for frozen source and retained reference input; not a new contextual compiler/extractor correctness theorem or coherent release replay. Existing formal parser proofs plus new circle theorems consume the retained nominal parser.')
(E/'parser-binding.json').write_text(json.dumps(result,indent=2)+'\n')
