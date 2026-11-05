from pathlib import Path
import subprocess,re,json,hashlib
E=Path(__file__).resolve().parent;revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
frozen=subprocess.check_output(['git','show',revision+':crates/aspis-r1-cost-probe/src/weights.rs'],text=True)
source=(E/'NIT_tail.rs.txt').read_text();flat=lambda s:re.sub(r'\s+','',s)
assert 'parts[0]=grouped_inactive_pair(self,f,&low);' in flat(frozen)
assert 'factored_s2_libra_weights(&ap0,&ap1,self.extra)' in flat(frozen)
assert 'Ok(sum)' in frozen
sig=re.search(r'fn factored_s2_libra_weights\(([^\n]*)',frozen).group(1)
assert 'extra:[K;2]' in flat(sig)
def validate(s):
 s=flat(s)
 for text in ['fnfactored(ap0:&[E;4],ap1:&[E;4],extra:[K;2],l:&mutTail)',
              'l.extra=extra;','parts[0]=group(w,f,low,l);','factored(ap0,ap1,w.extra,l)',
              'fnreturned_pair(sum:E)->Result<E,Error>{Ok(sum)}',
              'kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)',
              'kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)']:
  assert text in s,text
 assert '&[K;2]' not in s,'borrowed extra is not frozen interface'
 return True
assert validate(source)
mutations=[('owned-to-borrowed',source.replace('extra:[K;2],l:&mut Tail','extra:&[K;2],l:&mut Tail')),
 ('wrong-extra',source.replace('factored(ap0,ap1,w.extra,l)','factored(ap0,ap1,[K::ZERO;2],l)')),
 ('wrong-part',source.replace('parts[0]=group(w,f,low,l)','parts[1]=group(w,f,low,l)')),
 ('wrong-return',source.replace('fn returned_pair(sum:E)->Result<E,Error>{Ok(sum)}','fn returned_pair(sum:E)->Result<E,Error>{Ok(E::ZERO)}')),
 ('missing-KMX',source.replace('#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]',''))]
rejected=[]
for name,s in mutations:
 try:validate(s)
 except AssertionError:rejected.append(name)
 else:raise AssertionError('accepted mutation '+name)
out=dict(revision=revision,frozen_path='crates/aspis-r1-cost-probe/src/weights.rs',frozen_sha256=hashlib.sha256(frozen.encode()).hexdigest(),harness_sha256=hashlib.sha256(source.encode()).hexdigest(),factored_signature=sig,domain='w.variant == S2; two-fold path, f2048, canonical E arrays; w factors/points/extra raw unrestricted in caller observation',positive=True,rejected_mutations=rejected,scope='Exact grouped->parts0->factored stage plus isolated final Ok(sum), not whole pair')
(E/'NIT_NATIVE_SHAPE.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'positive':True,'controls_rejected':len(rejected)}))
