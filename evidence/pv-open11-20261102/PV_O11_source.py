from pathlib import Path
import re,json,hashlib
D=Path(__file__).parent
S=D/'inputs'
def strip(s):return re.sub(r'/\*.*?\*/|//[^\n]*','',s,flags=re.S)
def tok(s):return re.findall(r'::|=>|[A-Za-z_]\w*|\d+|[^\s]',strip(s))
def body(s,anchor):
 s=strip(s);a=s.index('{',s.index(anchor));n=0
 for i in range(a,len(s)):
  n+=(s[i]=='{')-(s[i]=='}')
  if n==0:return s[a:i+1]
 raise ValueError(anchor)
s=(S/'std-error.rs').read_text();packed=(S/'std-repr-bitpacked.rs').read_text();unix=(S/'std-unix-error.rs').read_text()
want='{ match self.repr.data() { ErrorData::Os(code) => sys::io::decode_error_kind(code), ErrorData::Custom(c) => c.kind, ErrorData::Simple(kind) => kind, ErrorData::SimpleMessage(m) => m.kind, } }'
checks={}
checks['complete_kind_body']=tok(body(s,'pub fn kind(&self)'))==tok(want)
checks['shared_data_borrow']=tok(body(packed,'pub(super) fn data(&self)'))==tok('{ unsafe { decode_repr(self.0, |c| &*c) } }')
# No dyn call, formatting, allocator, errno read, syscall, or Drop in kind/data.
checks['no_custom_payload_call']='ErrorData::Custom(c)=>c.kind,' in ''.join(tok(want))
checks['negative_dispatch_rejected']=tok(want.replace('c.kind','m.kind'))!=tok(body(s,'pub fn kind(&self)'))
# Exact platform selection must be bound before this can become a native law.
raw=body(unix,'pub fn decode_error_kind(')
arms=re.findall(r'libc::(E[A-Z0-9]+)\s*=>\s*(\w+)',raw)
checks['unix_default_retained']='_=>Uncategorized,' in ''.join(tok(raw))
checks['errno_not_read']='errno as libc::c_int' in raw and 'last_os_error' not in raw
j=dict(row='V176',toolchain='1.94.1',checks=checks,ok=all(checks.values()),kind_body=body(s,'pub fn kind(&self)'),data_body=body(packed,'pub(super) fn data(&self)'),decode_repr_body=body(packed,'unsafe fn decode_repr<'),unix_decoder_body=raw,simple_arms=arms,inputs={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in S.glob('std-*.rs')},classification='source dispatch census only; packed pointer/load, enum decoding, errno constants and native-to-model carrier installation remain separate until bound')
(D/'PV_O11_source.json').write_text(json.dumps(j,indent=2)+'\n'); print(json.dumps(dict(ok=j['ok'],checks=checks)));assert j['ok']
