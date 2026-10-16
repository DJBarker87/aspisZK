#!/usr/bin/env python3
"""Reproduce the naming-only discriminator expansion used by the joint parser proof."""
from pathlib import Path
import argparse,hashlib
SHA=lambda b:hashlib.sha256(b).hexdigest()
ORIGINAL='1a0da72bba235131e59061b0da65777cdbb85cc7c92673482ac149a3ac0c1646'
ADAPTED='1f2e779f9fa448e66597d09cfe226758829733a3f0ae4a1a07de4694953c8c7d'
extra='''def verifier.Error.read_discriminant : verifier.Error → Std.Isize
  | .Parse => 0#isize
  | .Semantic => 1#isize
  | .Transcript => 2#isize
  | .Relation => 3#isize
  | .Merkle => 4#isize
  | .Query => 5#isize
  | .Checkpoint => 6#isize
  | .Allocation => 7#isize

instance _root_.AspisR1EcheckCut.verifier.Error.instDiscriminant :
    Aeneas.Std.Discriminant verifier.Error Isize where
  read_discriminant := verifier.Error.read_discriminant

'''
def adapt(raw):
 assert SHA(raw)==ORIGINAL
 s=raw.decode();marker='@[discriminant isize]\ninductive verifier.Error'
 assert s.count(marker)==1
 s=s.replace(marker,'inductive verifier.Error',1)
 end='end AspisR1EcheckCut\n';assert s.count(end)==1
 out=s.replace(end,extra+end,1).encode();assert SHA(out)==ADAPTED
 inverse=out.decode().replace(extra,'',1).replace('inductive verifier.Error',marker,1).encode()
 assert inverse==raw
 return out
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--original',type=Path,required=True);p.add_argument('--adapted',type=Path,required=True);p.add_argument('--write',action='store_true');a=p.parse_args()
 out=adapt(a.original.read_bytes())
 if a.write:a.adapted.write_bytes(out)
 else:assert a.adapted.read_bytes()==out
 print('Verified exact names-only adapter and byte-exact inverse:',ADAPTED)
