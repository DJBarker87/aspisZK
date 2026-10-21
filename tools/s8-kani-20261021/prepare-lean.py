#!/usr/bin/env python3
"""Install complete extraction; only add missing local Option discriminant instance."""
from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s8-kani-20261021/extraction-complete/generated/S8OwnedP6';L=B/'lean/S8OwnedP6'
extra='''namespace S8OwnedP6

-- Runtime elaboration support: the emitted Option residual reads tag zero.
-- Local scope prevents discriminant collisions in downstream combined imports.
local instance optionDiscriminant {T : Type} : Discriminant (Option T) Isize where
  read_discriminant := fun x => match x with | none => 0#isize | some _ => 1#isize
'''
for name in ['Types','Funs']:
 s=(E/(name+'.lean')).read_text()
 if name=='Funs':s=s.replace('namespace S8OwnedP6',extra,1)
 p=L/(name+'.lean')
 if '--check' in sys.argv:assert p.read_text()==s,name
 else:p.write_text(s)
print('Complete emitted definitions match; only local Option discriminant support added')
