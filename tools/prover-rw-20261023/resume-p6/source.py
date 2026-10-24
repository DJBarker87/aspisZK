"""Generate prospective source and reversible metadata patches; no semantic erasure claim."""
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
P=D/'proof';P.mkdir(exist_ok=True)
original=(D.parent/'factory-state/preflight/lib.rs').read_text()
selected=original.replace('ProverRwFactoryState','ProverRwResumeP6')
(P/'selected.rs').write_text(selected)
patches=[]
def patch(s,old,new,label):
 assert s.count(old)==1,(label,s.count(old))
 patches.append(dict(label=label,before=old,after=new))
 return s.replace(old,new)
z=(D/'zeroize-original.rs.txt').read_text()
z=patch(z,'    fn zeroize(&mut self);','''    fn zeroize(&mut self);
    #[cfg(kani)]
    fn prover_rw_resume_p6_snapshot(&self) -> Option<ProverRwResumeP6::Snapshot> { None }
''','Zeroize typed observation default')
z=patch(z,'pub trait DefaultIsZeroes: Copy + Default + Sized {}','''pub trait DefaultIsZeroes: Copy + Default + Sized {
    #[cfg(kani)]
    fn prover_rw_resume_p6_byte(&self) -> Option<u8> { None }
}''','primitive observation default')
z=patch(z,'    u8, u16, u32, u64, u128, usize','    u16, u32, u64, u128, usize','u8 explicit impl expansion')
z=patch(z,'/// `PhantomPinned` is zero sized','''impl DefaultIsZeroes for u8 {
    #[cfg(kani)]
    fn prover_rw_resume_p6_byte(&self) -> Option<u8> { Some(*self) }
}

/// `PhantomPinned` is zero sized''','u8 typed safe observation')
z=patch(z,'''        volatile_write(self, Z::default());
        atomic_fence();
    }
}''','''        volatile_write(self, Z::default());
        atomic_fence();
    }
    #[cfg(kani)]
    fn prover_rw_resume_p6_snapshot(&self) -> Option<ProverRwResumeP6::Snapshot> {
        let mut bytes=[0u8;64];
        bytes[0]=self.prover_rw_resume_p6_byte()?;
        Some(ProverRwResumeP6::Snapshot { bytes, len: 1 })
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
    #[cfg(kani)]
    fn prover_rw_resume_p6_snapshot(&self) -> Option<ProverRwResumeP6::Snapshot> {
        if N != 32 && N != 64 { return None; }
        let mut bytes=[0u8;64];
        let mut i=0;
        while i<N {
            let element=self[i].prover_rw_resume_p6_snapshot()?;
            if element.len != 1 { return None; }
            bytes[i]=element.bytes[0];
            i+=1;
        }
        Some(ProverRwResumeP6::Snapshot { bytes, len: N })
    }
}''','array typed observation')
# Select exact Drop impl, not the other self.0.zeroize() implementations.
a=z.index('impl<Z> Drop for Zeroizing<Z>');b=z.index('\n}',a)+2
body=z[a:b]
assert body.count('        self.0.zeroize()')==1
newbody=body.replace('        self.0.zeroize()','''        #[cfg(kani)]
        let before=self.0.prover_rw_resume_p6_snapshot();
        self.0.zeroize();
        #[cfg(kani)]
        ProverRwResumeP6::record(before, self.0.prover_rw_resume_p6_snapshot());''')
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
    pub const fn prover_rw_resume_p6_from_repr(code: core::num::NonZeroI32) -> Self {
        Self(code)
    }
'''
assert g.count(needle)==1
modified=g.replace(needle,constructor)
assert modified.replace(constructor,needle)==g
(D/'getrandom-error-instrumented.rs.txt').write_text(modified)
meta=dict(schema='ProverRwResumeP6-source-v1',entry_revision='1097f5bef9f0ae52ac0c4df61857dc0d16e9bc26',
 source_before_sha256=sha(original.encode()),selected_sha256=sha(selected.encode()),
 rename={'before':'ProverRwFactoryState','after':'ProverRwResumeP6'},
 zeroize=dict(original_sha256=sha(restored.encode()),instrumented_sha256=sha(z.encode()),patches=patches),
 getrandom=dict(original_sha256=sha(g.encode()),instrumented_sha256=sha(modified.encode()),before=needle,after=constructor),
 semantic_erasure_proved=False,production_edited=False,print_axioms='N/A: reversible source generation')
(D/'source-map.json').write_text(json.dumps(meta,indent=2)+'\n')
print('Generated source with exact reverse-patch identity; semantic erasure OPEN')
