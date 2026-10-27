"""Build a complete scalar OS-code reference from pinned std source/errno ABI."""
from pathlib import Path
import json,re,sys
r=Path(__file__).resolve().parents[2];e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026/resumed144';s=(e/'kani-std-unix-mod.rs.txt').read_text();a=s.index('decode_error_kind(errno:');b=s.index('\n}\n',a);cut=s[a:b];codes=json.loads((e/'linux-errno.json').read_text());rows=[]
for names,kind in re.findall(r'((?:libc::\w+(?: \| )?)+) => (\w+),',cut):
 vals=[codes[n] for n in re.findall(r'libc::(\w+)',names)];rows.append((vals,kind))
assert any(vs==[codes['EAGAIN']] and k=='WouldBlock' for vs,k in rows);assert codes['EAGAIN']==codes['EWOULDBLOCK'];assert len({x for vs,k in rows for x in vs})==sum(len(vs) for vs,k in rows)
s='''\n#[cfg(kani)]
mod io_os_kind_scalar {
    use std::io::{Error,ErrorKind};
    fn expected(code:i32)->ErrorKind {
        match code {
'''
for vs,k in rows:s+='            '+' | '.join(map(str,vs))+'=>ErrorKind::'+k+',\n'
s+='''            _=>ErrorKind::Uncategorized,
        }
    }
    #[kani::proof]
    fn every_os_error_code_kind_and_payload() {
        let code:i32=kani::any();
        let error=Error::from_raw_os_error(code);
        assert!(error.raw_os_error()==Some(code));
        assert!(error.kind()==expected(code));
        assert!(error.get_ref().is_none());
    }
}
'''
p=r/'tools/prover-dict-20261026/proof-std-native/lib.rs';old=p.read_text();old=old.split('\n#[cfg(kani)]\nmod io_os_kind_scalar')[0];old=old.replace('#![cfg_attr(kani,feature(formatting_options))]','#![cfg_attr(kani,feature(formatting_options,io_error_more,io_error_inprogress,io_error_uncategorized))]');result=old+s
if '--check' in sys.argv:assert p.read_text()==result
else:p.write_text(result)
(e/'os-kind-table.json').write_text(json.dumps(dict(rows=[dict(codes=vs,kind=k) for vs,k in rows],default='Uncategorized',scope='All signed32 OS error codes only; full native Error dynamic representation not asserted'),indent=2)+'\n');print(len(rows),'arms')
