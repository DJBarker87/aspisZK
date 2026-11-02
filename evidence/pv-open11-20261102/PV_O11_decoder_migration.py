from pathlib import Path
import importlib.util,re,json,hashlib
D=Path(__file__).parent
spec=importlib.util.spec_from_file_location('pv_source',D/'PV_O11_source.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
old=(D/'inputs/std-repr-bitpacked.rs').read_text();new=(D/'inputs/extractor-core-error.rs').read_text();deployed=(D/'inputs/std-error.rs').read_text()
a=m.body(old,'fn kind_from_prim(');b=m.body(new,'pub const fn from_prim(')
# Erase only the compile-time exhaustiveness assertion. It has no runtime call.
def erase_compile_time(s):
 s=m.strip(s);a=s.index('const _: fn(e: $Enum)');o=s.index('{',a);n=0
 for i in range(o,len(s)):
  n+=(s[i]=='{')-(s[i]=='}')
  if n==0:
   assert s[i+1:].lstrip().startswith(';')
   j=s.index(';',i+1)+1
   return s[:a]+s[j:]
 raise ValueError('const witness not closed')
# Enum source order is the discriminant authority, not the decoder macro list order.
def variants(s):
 body=m.body(s,'pub enum ErrorKind')
 return re.findall(r'^\s*([A-Z][A-Za-z0-9_]*)\s*,',body,re.M)
checks=dict(runtime_body_tokens_equal=m.tok(erase_compile_time(a))==m.tok(erase_compile_time(b)),enum_order_equal=variants(deployed)==variants(new),variant_count_42=len(variants(new))==42)
x=m.body((D/'inputs/extractor-std-repr-bitpacked.rs').read_text(),'unsafe fn decode_repr<');y=m.body(old,'unsafe fn decode_repr<')
checks['only_decode_call_relocated']=m.tok(x.replace('ErrorKind::from_prim(kind_bits)','kind_from_prim(kind_bits)'))==m.tok(y)
j=dict(checks=checks,ok=all(checks.values()),deployed_decoder_body=a,extractor_decoder_body=b,variants=variants(new),interpretation='structural argument for relocation of an unchanged 42-variant decoder; the erased const is an exhaustiveness type check, not runtime execution. No native Error carrier or pointer/load/Drop association is supplied.',evidence_class='script-checked structural argument; not a machine proof, extraction credit, or row restoration')
(D/'PV_O11_decoder-migration.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(checks));assert j['ok']
