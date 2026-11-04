"""Exact source-site checks for partial nonempty geometry packets."""
from NET_prefix_source import tok,REV,E,R
import subprocess,json,hashlib

def check(native=None,frozen=None):
 if native is None:native=(E/'NET_geometry.rs.txt').read_text()
 path='crates/aspis-r1-cost-probe/src/verifier.rs'
 if frozen is None:frozen=subprocess.check_output(['git','show',REV+':'+path],cwd=R,text=True)
 helper=native[native.index(' if values.iter()'):native.index('\n Ok(())')]
 helper=helper.replace('#[cfg(NET_bad_option)] {return Ok(());}','')
 helper=helper.replace('lines.push(values[4]);','line_z_values.push(line_z);')
 source=frozen[frozen.index('if values.iter()'):frozen.index('\n        }',frozen.index('if values.iter()'))]
 assert tok(helper)==tok(source),'gather write/order/zero guard differs'
 assert 'let values=[circle_x,circle_y,line_x,line_y,line_z];' in frozen
 start=native.index(' inverse[i]=NET_back_product(');end=native.index('\n suffix\n}',start)
 back=native[start:end]
 back=back.replace('inverse[i]=NET_back_product(suffix,prefixes[i],M31(reply[0]),log);','flat_inverse[i]=suffix_inverse.mul(prefixes[i]);')
 back=back.replace('let suffix=NET_back_product(suffix,flat[i],M31(reply[1]),log);','suffix_inverse=suffix_inverse.mul(flat[i]);')
 a=frozen.index('flat_inverse[i]=suffix_inverse.mul(prefixes[i]);');b=frozen.index('\n        }',a)
 assert tok(back)==tok(frozen[a:b]),'backward write/order/product differs'
 assert 'let mut flat=Vec::with_capacity((end-start)*5);' in frozen
 assert 'let mut line_z_values=Vec::with_capacity(end-start);' in frozen
 assert 'for i in (0..flat.len()).rev()' in frozen
 assert not any(t in native for t in ['static mut','UnsafeCell','RefCell','Atomic','Option<fn','stub_verified','proof_for_contract'])
 return dict(frozen_revision=REV,source_file=path,native_sha256=hashlib.sha256(native.encode()).hexdigest(),gather_after_erasure=hashlib.sha256(source.encode()).hexdigest(),backward_after_erasure=hashlib.sha256(frozen[a:b].encode()).hexdigest(),status='PARTIAL_ONLY; inverse and full for_range composition remain OPEN',scope='one query append and one reverse-cell step; native products opaque with local log')
if __name__=='__main__':print(json.dumps(check(),indent=1))
