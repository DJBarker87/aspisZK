"""Generate prospective source and reversible metadata patches; no semantic erasure claim."""
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
P=D/'proof';P.mkdir(exist_ok=True)
original=(D.parent/'factory-state/preflight/lib.rs').read_text()
selected=original.replace('ProverRwFactoryState','ProverRwResumeScalar')
(P/'selected.rs').write_text(selected)
patches=[]
def patch(s,old,new,label):
 assert s.count(old)==1,(label,s.count(old))
 patches.append(dict(label=label,before=old,after=new))
 return s.replace(old,new)
z=(D/'zeroize-original.rs.txt').read_text()
z=patch(z,'    fn zeroize(&mut self);','''    fn zeroize(&mut self);
    #[cfg(any(kani, prover_rw_resume_scalar))]
    fn prover_rw_resume_scalar_observe(&self, _j: usize) -> ProverRwResumeScalar::Observation {
        ProverRwResumeScalar::Observation { len: 0, low: 0, high: 0 }
    }
    #[cfg(any(kani, prover_rw_resume_scalar))]
    fn prover_rw_resume_scalar_byte(&self) -> Option<u8> { None }
''','Zeroize typed observation default')
z=patch(z,'pub trait DefaultIsZeroes: Copy + Default + Sized {}','''pub trait DefaultIsZeroes: Copy + Default + Sized {
    #[cfg(any(kani, prover_rw_resume_scalar))]
    fn prover_rw_resume_scalar_byte(&self) -> Option<u8> { None }
}''','primitive observation default')
z=patch(z,'    u8, u16, u32, u64, u128, usize','    u16, u32, u64, u128, usize','u8 explicit impl expansion')
z=patch(z,'/// `PhantomPinned` is zero sized','''impl DefaultIsZeroes for u8 {
    #[cfg(any(kani, prover_rw_resume_scalar))]
    fn prover_rw_resume_scalar_byte(&self) -> Option<u8> { Some(*self) }
}

/// `PhantomPinned` is zero sized''','u8 typed safe observation')
z=patch(z,'''        volatile_write(self, Z::default());
        atomic_fence();
    }
}''','''        volatile_write(self, Z::default());
        atomic_fence();
    }
    #[cfg(any(kani, prover_rw_resume_scalar))]
    fn prover_rw_resume_scalar_byte(&self) -> Option<u8> {
        <Z as DefaultIsZeroes>::prover_rw_resume_scalar_byte(self)
    }
}''','scalar typed observation')
z=patch(z,'''impl<Z, const N: usize> Zeroize for [Z; N]
where
    Z: Zeroize,
{
    fn zeroize(&mut self) {
        self.iter_mut().zeroize();
    }
}''','''impl<Z, const N: usize> Zeroize for [Z; N]
where
    Z: Zeroize,
{
    fn zeroize(&mut self) {
        self.iter_mut().zeroize();
    }
    #[cfg(any(kani, prover_rw_resume_scalar))]
    fn prover_rw_resume_scalar_observe(&self, j: usize) -> ProverRwResumeScalar::Observation {
        // Range guard precedes both typed indexing operations; no observation loop.
        if (N != 32 && N != 64) || j >= 32 {
            return ProverRwResumeScalar::Observation { len: 0, low: 0, high: 0 };
        }
        let low = match self[j].prover_rw_resume_scalar_byte() {
            Some(byte) => byte,
            None => return ProverRwResumeScalar::Observation { len: 0, low: 0, high: 0 },
        };
        let high = if N == 64 {
            match self[j + 32].prover_rw_resume_scalar_byte() {
                Some(byte) => byte,
                None => return ProverRwResumeScalar::Observation { len: 0, low: 0, high: 0 },
            }
        } else { 0 };
        ProverRwResumeScalar::Observation { len: N, low, high }
    }
}''','array typed observation')
# Select exact Drop impl, not the other self.0.zeroize() implementations.
a=z.index('impl<Z> Drop for Zeroizing<Z>');b=z.index('\n}',a)+2
body=z[a:b]
assert body.count('        self.0.zeroize()')==1
newbody=body.replace('        self.0.zeroize()','''        #[cfg(any(kani, prover_rw_resume_scalar))]
        let j=ProverRwResumeScalar::coordinate();
        #[cfg(any(kani, prover_rw_resume_scalar))]
        let before=self.0.prover_rw_resume_scalar_observe(j);
        self.0.zeroize();
        #[cfg(any(kani, prover_rw_resume_scalar))]
        ProverRwResumeScalar::record(before, self.0.prover_rw_resume_scalar_observe(j));''')
z=patch(z,body,newbody,'real Drop pre/post hooks')
module=(D/'metadata.rs.txt').read_text()
z=patch(z,'/// Trait for securely erasing values from memory.',module+'\n/// Trait for securely erasing values from memory.','metadata module')
restored=z
for p in reversed(patches):
 assert restored.count(p['after'])==1,p['label']
 restored=restored.replace(p['after'],p['before'])
assert restored==(D/'zeroize-original.rs.txt').read_text()
(D/'zeroize-instrumented.rs.txt').write_text(z)
g=(D/'getrandom-error-original.rs.txt').read_text()
needle='impl Error {'
constructor='''impl Error {
    #[cfg(all(kani, target_os="linux", target_arch="x86_64"))]
    pub const fn prover_rw_resume_scalar_from_repr(code: core::num::NonZeroI32) -> Self {
        Self(code)
    }
'''
assert g.count(needle)==1
modified=g.replace(needle,constructor)
assert modified.replace(constructor,needle)==g
(D/'getrandom-error-instrumented.rs.txt').write_text(modified)
meta=dict(schema='ProverRwResumeScalar-source-v1',entry_revision='7e900bb53455a1758fe24014d1987f08d6cbb242',
 source_before_sha256=sha(original.encode()),selected_sha256=sha(selected.encode()),
 rename={'before':'ProverRwFactoryState','after':'ProverRwResumeScalar'},
 zeroize=dict(original_sha256=sha(restored.encode()),instrumented_sha256=sha(z.encode()),patches=patches),
 getrandom=dict(original_sha256=sha(g.encode()),instrumented_sha256=sha(modified.encode()),before=needle,after=constructor),
 semantic_erasure_proved=False,production_edited=False,print_axioms='N/A: reversible source generation')
(D/'source-map.json').write_text(json.dumps(meta,indent=2)+'\n')
print('Generated source with exact reverse-patch identity; semantic erasure OPEN')
