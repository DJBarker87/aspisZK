from pathlib import Path
import hashlib,json,sys
w=Path(__file__).resolve().parent; kit=w/'input'; pins=json.loads((kit/'source-pins.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
errs=[]
for n,h in pins['kit_files'].items():
 p=kit/n
 if not p.is_file() or sha(p)!=h: errs.append('kit hash '+n)
src=w/'source-snapshot/weights.rs'
if not src.is_file() or sha(src)!=pins['source_snapshot']['sha256']: errs.append('source snapshot hash')
text=(kit/'lib.rs').read_text(); rust=src.read_text()
def extract(t,needle):
 i=t.index(needle); start=t.index('{',i); d=0; instr=False; esc=False
 for j in range(start,len(t)):
  c=t[j]
  if instr:
   if esc: esc=False
   elif c=='\\': esc=True
   elif c=='\"': instr=False
   continue
  if c=='\"': instr=True; continue
  if c=='{': d+=1
  elif c=='}':
   d-=1
   if d==0:return t[i:j+1]
 raise ValueError(needle)
for name,needle in [('kpowers','pub fn kpowers<const N:usize>'),('factored_s2_libra_weights','fn factored_s2_libra_weights('),('Weights::scalar_factor','fn scalar_factor(')]:
 expected=extract(rust,needle)
 if text.count(expected)!=1: errs.append('body count mismatch '+name)
 cut=pins['source_cuts'][name]
 if hashlib.sha256(src.read_bytes()[cut['start_byte']:cut['end_byte_exclusive']]).hexdigest()!=cut['sha256']: errs.append('span hash '+name)
if errs: print('\n'.join(errs));sys.exit(1)
print('PASS exact source-cut bodies: kpowers, factored_s2_libra_weights, Weights::scalar_factor')

# Pair is deliberately recorded as a candidate; its body must not be mistaken
# for the frozen method. Check both pins and require the expected mismatch.
method='pub fn pair(&self,alpha:&[E],f:&[u8],kappa:E)'
candidate=extract(text,method).encode()
frozen=extract(rust,method).encode()
if hashlib.sha256(candidate).hexdigest()!=pins['candidate_method_sha256']:
 errs.append('candidate Pair method hash mismatch')
if hashlib.sha256(frozen).hexdigest()!=pins['frozen_pair_method_sha256']:
 errs.append('frozen Pair method hash mismatch')
if candidate==frozen:
 errs.append('candidate Pair unexpectedly identical; update provenance review')
