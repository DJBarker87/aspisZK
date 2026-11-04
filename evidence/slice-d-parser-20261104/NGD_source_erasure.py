"""Token-level local-record instrumentation check; not a semantic bridge.

Frozen source is a committed input pinned to 4bb3b3f. Erasure only substitutes
named callee calls. A changed caller condition or borrowed window is rejected.
"""
from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent

def body(s,name):
 m=re.search(r'\bfn\s+'+re.escape(name)+r'\b',s);assert m,name
 a=s.index('{',m.end());depth=1;i=a+1
 while depth:
  depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[a+1:i-1]
def tokens(s):
 s=re.sub(r'//[^\n]*|/\*.*?\*/','',s,flags=re.S)
 ts=re.findall(r'[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[^\s]',s)
 return [x for i,x in enumerate(ts) if not(x==',' and i+1<len(ts) and ts[i+1] in ['}',')',']'])]
def equal(a,b):return tokens(a)==tokens(b)
def check(frozen,native):
 parse=body(native,'native_parse_record').replace('validate_capture(row, payload, log)','validate_record_fields(row, payload)')
 at=body(native,'native_parse_at').replace('parse_capture(row, framed, log)','parse_record(row, framed)')
 assert equal(parse,body(frozen,'parse_record')),'parse_record caller differs after erasure'
 assert equal(at,body(frozen,'parse_record_at')),'parse_record_at caller differs after erasure'
 # Exact native one-assignment cut, before normalization of the token fields.
 actual=body(frozen,'decode_k');a=actual.index('out[value]');b=actual.index(';',a)+1
 stmt=actual[a:b].replace('row: self.row','row')
 assert tokens(stmt)==tokens(body(native,'decode_source_step').removesuffix('Ok(())\n').strip().removesuffix('Ok(())').strip()),'decode assignment differs'
 return {'parse_record':parse,'parse_record_at':at,'decode_assignment':stmt}
if __name__=='__main__':
 frozen=(E/'NGD_FROZEN_WIRE.rs.txt').read_text();native=json.loads((E/'NGD_NATIVE_INPUTS.json').read_text())['crates/aspis-r1-cost-probe/src/NGD_wire.rs']
 b=check(frozen,native);controls=[]
 for label,old,new in [('payload_window','let payload = &record[5..]','let payload = &record[6..]'),('forwarding_window','.get(offset..offset + length)','.get(0..offset + length)'),('decode_index','out[value]=QM31','out[0]=QM31')]:
  assert old in native,label
  try:check(frozen,native.replace(old,new));raise RuntimeError('Accepted corrupt caller '+label)
  except AssertionError:controls.append({'mutation':label,'rejected':True})
 (E/'NGD_SOURCE_ERASURE.json').write_text(json.dumps({'status':'PASS','frozen_revision':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','frozen_sha256':hashlib.sha256(frozen.encode()).hexdigest(),'native_sha256':hashlib.sha256(native.encode()).hexdigest(),'erased_tokens':{k:tokens(v)for k,v in b.items()},'controls':controls,'semantic_transport':'OPEN; token identity does not establish Kani instrumentation or cohort composition'},indent=2)+'\n')
 print('PASS: two caller bodies, one assignment, three rejected mutations; no composed closure added')
