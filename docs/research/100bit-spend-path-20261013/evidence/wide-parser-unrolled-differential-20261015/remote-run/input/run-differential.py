#!/usr/bin/env python3
"""Capped, source-pinned release-mode differential for unrolled WideExact."""
import hashlib, json, os, subprocess, sys
from pathlib import Path
KIT=Path(__file__).resolve().parent
EXPECTED={
 'baseline.rs':'28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea',
 'baseline/wide_exact.rs':'56c26ce33cd0caee95f33474bfc351c5409503b6af665dba7c8837d6ec1068ea',
 'field.rs':'28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea',
 'field/wide_exact.rs':'6260fa9d179328714e7df59640abb7a76a326e98900993ce7d3da98c6411d10b',
 'source-pins.json':'22a13f05ca1457d01861a1d586000d71015fc242182dbbb705fdf61f3d345c17',
 'candidate.patch':'e4b1dd436d2cf2ebedfdd10aeffef9bf69b5efe1e9eeea78a4639081e62de239',
 'differential.rs':'a52d1e9159e70dcaa229ac49a5d4da0e2ec96a31852a7553b83f6878a8ce7bed',
}
RUST_COMMIT='14210df0e27ccd7d9e6a05b8085cbd438e4bbc65'
TEST='unrolled_wideexact_parser_and_limbs_match_baseline'
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def timed(label,cmd,env):
 p=KIT/'results'/f'{label}.time.log'; r=subprocess.run(['/usr/bin/time','-v','-o',str(p),*cmd],cwd=KIT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (KIT/'results'/f'{label}.log').write_text(r.stdout)
 return {'label':label,'command':cmd,'exit_status':r.returncode,'stdout':f'results/{label}.log','time_log':f'results/{label}.time.log'}
def main():
 (KIT/'results').mkdir(exist_ok=False)
 inputs={k:digest(KIT/k) for k in EXPECTED}
 mismatch={k:(v,inputs[k]) for k,v in EXPECTED.items() if v is not None and v!=inputs[k]}
 if mismatch: raise SystemExit(f'input SHA-256 mismatch: {mismatch}')
 env=os.environ.copy();env['PATH']='/home/dombarker/.cargo/bin:/usr/bin:/bin';env['RUSTUP_TOOLCHAIN']='nightly-2026-06-01'
 commands=[]
 def save():
  data={'toolchain':'nightly-2026-06-01','rustc_commit_hash_expected':RUST_COMMIT,'inputs':inputs,'commands':commands,'coverage':{'input_lengths_inclusive':[0,64],'single_byte_values':256,'single_byte_positions':32,'limb_boundaries':[0,1,'P-1','P','P+1','u32::MAX'],'pairwise_boundary_limb_combinations':True,'seeded_random_vectors_per_length':256,'canonical_eight_limb_vectors':4096,'from_limbs_checked_for_every_exact_32_byte_vector':True},'expected_input_vectors':30055,'expected_parser_calls':60110,'expected_from_limbs_vectors':13607,'expected_from_limbs_calls':27214}
  (KIT/'results/run.json').write_text(json.dumps(data,indent=2)+'\n')
 c=timed('rustc-version',['rustup','run','nightly-2026-06-01','rustc','--version','--verbose'],env);commands.append(c);save()
 if c['exit_status']: raise SystemExit(c['exit_status'])
 if f'commit-hash: {RUST_COMMIT}' not in (KIT/'results/rustc-version.log').read_text(): raise SystemExit('pinned rustc commit mismatch')
 binary=KIT/'results/unrolled-wide-parser-tests'
 c=timed('compile',['rustup','run','nightly-2026-06-01','rustc','--test','--edition=2021','-C','opt-level=3','-C','overflow-checks=yes','differential.rs','-o',str(binary)],env);commands.append(c);save()
 if c['exit_status']==0:
  c=timed('test',[str(binary),'--exact',TEST,'--nocapture','--test-threads=1'],env);commands.append(c);save()
 return max(x['exit_status'] for x in commands)
if __name__=='__main__':sys.exit(main())
