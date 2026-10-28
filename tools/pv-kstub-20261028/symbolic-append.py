"""Strengthen the unrun fixed append gate with one arbitrary-length append."""
from pathlib import Path
import json,re,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-kstub-20261028');p=D/'cblib/lib.rs';s=p.read_text()
a=s.index('fn push_bytes()');b=s.index('\n#[kani::proof]',a)
old=s[a:b];new='''fn push_bytes() {
        let raw:[u8;2]=kani::any();let tail:[u8;1]=kani::any();
        let n:usize=kani::any();let m:usize=kani::any();
        kani::assume(n<=2 && m<=1);
        if let (Ok(mut s),Ok(t))=(String::from_utf8(raw[..n].to_vec()),std::str::from_utf8(&tail[..m])) {
            let mut reference=raw[..n].to_vec();reference.extend_from_slice(&tail[..m]);
            s.push_str(t);assert_eq!(s.as_bytes(),reference.as_slice());
        }
    }'''
assert 'let n:usize' not in old,'already strengthened; do not edit twice'
p.write_text(s[:a]+new+s[b:])
(D/'symbolic-append.json').write_text(json.dumps(dict(harness='resume8_links::push_bytes',before=old,after=new,before_sha256=hashlib.sha256(old.strip().encode()).hexdigest(),after_sha256=hashlib.sha256(new.encode()).hexdigest(),domain='arbitrary symbolic UTF8 prefix raw[..n], n<=2; arbitrary symbolic UTF8 tail[..m], m<=1; exactly one append',original_domain_instance='n=2,m=1 gives original index165 property without changing calls or expected byte relation',negative='push_bytes_negative remains original concrete n=2,m=1 nonempty fixture and negates the same equality',existing_runs_changed=[],reason='LEAD note under (r\u2032), KMZ symbolic-length single append'),indent=2)+'\n')
print('Prepared symbolic append; no verification launched')
