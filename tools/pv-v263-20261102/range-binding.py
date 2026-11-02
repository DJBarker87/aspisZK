"""Mechanical source-shape gate for the pure range helper ONLY (own-1)."""
from pathlib import Path
import re,json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-v263-20261102';src=E/'inputs/docs/research/v8-r0-zk-20261009/c3/check/src/native_workers.rs';s=src.read_text()
body=s[s.index('pub fn range('):s.index('pub fn is_worker()')]
expected='''pub fn range(n: usize, k: usize) -> (usize, usize) {
 assert!(k < THREADS);
 let q = n / THREADS;
 let r = n % THREADS;
 let start = q * k + core::cmp::min(k,r);
 (start, start + q + (k < r) as usize)
}'''
tokens=lambda s:re.findall(r'[A-Za-z_][A-Za-z_0-9]*|\d+|\S',s)
assert tokens(body)==tokens(expected)
assert 'pub const THREADS: usize = 16;' in s
model=R/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_WorkRange35.lean';m=model.read_text();assert 'def start (n k : Nat) : Nat := (n/16)*k+min k (n%16)' in m;assert 'def width (n k : Nat) : Nat := n/16 + if k<n%16 then 1 else 0' in m
out=dict(evidence_class='structural argument (own-1), pure range helper only',source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),body_token_sha256=hashlib.sha256('\0'.join(tokens(body)).encode()).hexdigest(),model_sha256=hashlib.sha256(model.read_bytes()).hexdigest(),steps=[['assert k<THREADS','PV_V263_Range hk'],['q=n/16; r=n%16','fixed nonzero divisor 16'],['q*k+min(k,r)','WorkRange35.start; Range.intermediates proves each arithmetic intermediate <=n'],['start+q+(k<r) as usize','start+width; Boolean cast is 0/1; Range.usize_safe'],['tuple return','same pair, no stores through mutable borrows, no allocation or drop glue']],retained=['compiler preservation V370','all worker/TLS/spawn/join/allocator/unwind/diagnostic associations','actual capture Nonempty P'],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
(E/'range-binding.json').write_text(json.dumps(out,indent=2)+'\n');print(out['evidence_class'])
