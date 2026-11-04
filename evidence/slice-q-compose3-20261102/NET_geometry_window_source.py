from NET_geometry_source import *
import lzma

def check_window(native=None):
 if native is None:native=(E/'NET_geometry.rs.txt').read_text()
 source=check(native)
 a=inputs=json.loads(lzma.decompress((E/'NET_K090_INPUTS.json.xz').read_bytes()))
 kmx=a['NET_src/KMX_stubs.rs'];assert hashlib.sha256(kmx.encode()).hexdigest()=='ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138'
 assert 'dst.reserve(src.len());let mut i=0;while i<src.len(){dst.push(src[i]);i+=1;}' in kmx
 first=native.index(' dst.push(src[i]);',native.index('fn NET_extend_step('));last=native.index('\n i\n}',first)
 erased=native[first:last].replace('let i=i+1;','i+=1;')
 assert tok(erased)==tok('dst.push(src[i]);i+=1;')
 assert 'dst.reserve(5);' in native and 'src:&[M31;5]' in native
 assert 'kani::assume(t<5);let len=5*k+t;' in native
 source.update(kmx_source_sha256=hashlib.sha256(kmx.encode()).hexdigest(),one_native_iteration=True,scope='reserve(5) separately; one native push at arbitrary inner offset t<5; SAME original gather harness names, changed proof shape, not renaming',root_status='OPEN')
 return source
if __name__=='__main__':print(json.dumps(check_window(),indent=1))
