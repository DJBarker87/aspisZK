from pathlib import Path
import sys
r=Path(sys.argv[1]);src=r/'crates/aspis-r1-cost-probe/src'
p=src/'lib.rs';s=p.read_text();assert 'pub mod host_work' not in s;s+='\n// Fixed public-shape scheduling for the host CT adoption candidate.\n#[cfg(feature="ct-host-prover")]\npub mod host_work;\n';p.write_text(s)
(src/'host_work.rs').write_text('''//! Fixed public work ranges; no operand-dependent work stealing or cancellation.
use alloc::vec::Vec;
#[path="../../../docs/research/v8-r0-zk-20261009/c3/check/src/native_workers.rs"]
mod pool;
#[cfg(feature="public-work-trace")]
static TRACE: std::sync::Mutex<Vec<[usize;6]>> = std::sync::Mutex::new(Vec::new());
/// Only public stage/shape/range and completed callback counts, never operands.
#[cfg(feature="public-work-trace")]
pub fn take_trace() -> Vec<[usize;6]> { core::mem::take(&mut *TRACE.lock().unwrap()) }
pub(crate) fn map<T:Send,F:Fn(usize)->T+Sync>(_stage:usize,n:usize,f:F)->Vec<T> {
    let chunks=pool::ordered_families(pool::THREADS,|k| {
        let (a,b)=pool::range(n,k);
        let mut out=Vec::with_capacity(b-a);
        let mut completed=0;
        for i in a..b {out.push(f(i));completed+=1;}
        (out,completed)
    });
    let mut out=Vec::with_capacity(n);
    for (k,(mut chunk,completed)) in chunks.into_iter().enumerate() {
        #[cfg(feature="public-work-trace")]
        {let (a,b)=pool::range(n,k);TRACE.lock().unwrap().push([_stage,n,k,a,b,completed]);}
        #[cfg(not(feature="public-work-trace"))]
        let _=(k,completed);
        out.append(&mut chunk);
    }
    out
}
''')
p=r/'crates/aspis-r1-cost-probe/Cargo.toml';s=p.read_text().replace('[features]','[features]\n# Audit only: public schedule and callback-count receipts; no operands.\npublic-work-trace = ["ct-host-prover"]',1);p.write_text(s)
p=src/'host_sumcheck.rs';s=p.read_text().replace('mut oracle: impl FnMut(&[QM31; 10]) -> Result<QM31, Error>,','oracle: impl Fn(&[QM31; 10]) -> Result<QM31, Error> + Sync,');a=s.index('            for (sample, value)');b=s.index('            let polynomial',a);old=s[a:b]
s=s[:a]+'''            #[cfg(feature="ct-host-prover")]
            {
                let assignments=1usize<<remaining;
                let evaluations=crate::host_work::map(100+round,28*assignments,|i| {
                    let sample=i/assignments;let assignment=i%assignments;
                    let mut at=point;
                    at[round]=QM31::from_cm31(CM31::from_m31(M31(sample as u32)));
                    for offset in 0..remaining {
                        at[round+1+offset]=if (assignment>>(remaining-1-offset))&1==0 {QM31::ZERO}else{QM31::ONE};
                    }
                    oracle(&at)
                });
                // Same sample and assignment order, including error selection.
                for (i,value) in evaluations.into_iter().enumerate() {
                    values[i/assignments]=values[i/assignments].add(value?);
                }
            }
            #[cfg(not(feature="ct-host-prover"))]
            {
'''+old+'''            }
'''+s[b:];p.write_text(s)
p=src/'host_commitment.rs';s=p.read_text();a=s.index('        for &l in &lanes {');b=s.index('        let mut leaves',a);old=s[a:b]
new='''        #[cfg(feature="ct-host-prover")]
        {
            // Validate in source order before launching a public lane partition.
            for &l in &lanes {
                if messages[l].iter().any(|x|x.to_limbs()[if l<26 {1}else{4}..].iter().any(|&d|d!=0)) {
                    return Err(Error::WrongField);
                }
                saved.push(messages[l]);
            }
            let encoded=crate::host_work::map(200,lanes.len(),|i| {
                let l=lanes[i];
                let coefficients=variant.coefficients(&messages[l]);
                if l<26 {
                    domain.encode(&coefficients.map(|x|M31(x.to_limbs()[0]))).map(Word::Base)
                } else {
                    domain.encode(&coefficients.map(|x|x.c0())).map(Word::Secure)
                }
            });
            for word in encoded {words.push(word?);}
        }
        #[cfg(not(feature="ct-host-prover"))]
        {
'''+old+'        }\n'
s=s[:a]+new+s[b:];p.write_text(s)
