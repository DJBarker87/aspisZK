from pathlib import Path
import hashlib,json,subprocess,re
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2c-20261028');lib=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library')
paths=['alloc/src/vec/in_place_collect.rs','alloc/src/vec/spec_from_iter.rs','alloc/src/vec/spec_from_iter_nested.rs','alloc/src/vec/spec_extend.rs','alloc/src/vec/into_iter.rs','alloc/src/raw_vec/mod.rs','alloc/src/alloc.rs','core/src/iter/adapters/flatten.rs','core/src/iter/adapters/filter.rs','core/src/iter/adapters/map.rs','core/src/array/iter.rs','core/src/slice/sort/unstable/mod.rs']
records=[];out=D/'rdb2d-stdlib';out.mkdir(exist_ok=True)
for p in paths:
 b=(lib/p).read_bytes();records.append(dict(path=p,sha256=hashlib.sha256(b).hexdigest()));(out/p.replace('/','_')).write_bytes(b)
f=(lib/'core/src/iter/adapters/flatten.rs').read_text();assert 'InPlaceIterable' not in f
for name in ['SourceIter for FlatMap','TrustedLen for FlatMap']:assert name in f
filter_text=(lib/'core/src/iter/adapters/filter.rs').read_text();assert 'InPlaceIterable for Filter' in filter_text
n=(lib/'alloc/src/vec/spec_from_iter_nested.rs').read_text();assert 'I: TrustedLen<Item = T>' in n and '(_, Some(upper)) => Vec::with_capacity(upper)' in n
p=lib/'alloc/src/vec/in_place_collect.rs';t=p.read_text();assert 'if needs_realloc::<I::Src, T>(src_cap, dst_cap)' in t and 'src_sz % dest_sz == 0' in t
r=subprocess.run([str(D/'target-weights/release/forest'),'3','rows'],capture_output=True,text=True);assert r.returncode==-6
r2=subprocess.run([str(D/'target-weights/release/forest'),'3','mask'],capture_output=True,text=True);assert r2.returncode==-6
j=dict(stdlib=records,negative_trait_check='FlatMap and Flatten have no InPlaceIterable impl in pinned flatten.rs; SourceIter+TrustedLen present',filter='Filter implements InPlaceIterable; equal sizes8 avoid needs_realloc',flatmap='TrustedLen SpecFromIterNested: upper136*2=272 u16; allocate544; drop source cap254*8=2032',third_failure=[dict(mode=m,exit=x.returncode,stdout=x.stdout,stderr=x.stderr)for m,x in [('rows',r),('mask',r2)]],finite_validation_only=True)
(D/'rdb2d-collector-binding.json').write_text(json.dumps(j,indent=2));print(json.dumps(j),flush=True)
