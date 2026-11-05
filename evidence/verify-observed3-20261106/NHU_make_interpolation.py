from pathlib import Path
import subprocess,hashlib,json
E=Path(__file__).resolve().parent;R=E.parents[1];rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';path='crates/aspis-statement/src/state_only_poseidon.rs';s=subprocess.check_output(['git','show',rev+':'+path],cwd=R).decode();a=s.index('fn interpolate_three_constant_limb(');b=s.index('\n}',a)+2;body=s[a:b];out=body.replace('fn interpolate_three_constant_limb(','fn NHU_interpolation_cut(').replace(') -> M31 {','log:&mut InterpolationLog) -> M31 {')
for i in range(3):
 old=f'u64::from(weight{i}) * u64::from(constant{i})';assert out.count(old)==1;out=out.replace(old,f'raw_product(weight{i},constant{i},log)')
out=out.replace('M31::reduce_u64(','raw_reduce(');out=out.replace('\n    )','\n    log)')
revout=out.replace('fn NHU_interpolation_cut(','fn interpolate_three_constant_limb(').replace('log:&mut InterpolationLog) -> M31 {',') -> M31 {').replace('raw_reduce(','M31::reduce_u64(').replace('\n    log)','\n    )')
for i in range(3):revout=revout.replace(f'raw_product(weight{i},constant{i},log)',f'u64::from(weight{i}) * u64::from(constant{i})')
assert revout==body
(E/'NHU_interpolation_body.rs.txt').write_text(out+'\n');(E/'NHU_INTERPOLATION_ERASURE.json').write_text(json.dumps(dict(status='PASS',revision=rev,path=path,source_sha256=hashlib.sha256(s.encode()).hexdigest(),body_sha256=hashlib.sha256(body.encode()).hexdigest(),cuts=['u64 widened product0','u64 widened product1','u64 widened product2','M31::reduce_u64'],method='exact frozen source body; local opaque product/reducer logs, native bounded additions; no multiplication in Kani'),indent=1)+'\n')
