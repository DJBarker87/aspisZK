#!/usr/bin/env python3
"""Replace the generated (stage-1/2) M31.mul theorem in PRVEq_AspisV8R19_<M>FieldSlice_j1.lean by the P3b proof (PCVB_ M31.fast_chain), names renamed to the _j1 tag.
Only the theorem text is transplanted; PCVB_M31 lemmas come in through the generator's --preamble (copied from the same P3b file)."""
import re,sys
sys.dont_write_bytecode=True
for m in sys.argv[1:]:
    if open(f'PRVEq_AspisV8R19_{m}FieldSlice_j1.lean').read().count('P3b: fresh M31.mul'): continue
    old=open(f'../prov-p3b-20261109/PRVEq_AspisV8R19_{m}FieldSlice_P3.lean').read()
    a=old.index('set_option maxHeartbeats 200000 in\n/-- P3b: fresh M31.mul')
    pm=f'#print axioms PRVEq.AspisV8R19.{m}FieldSlice.'+('aspis_core.' if m=='Guarded' else '')+'field.M31.mul'
    b=old.index(pm)+len(pm)
    blk=old[a:b].replace('aspis_core.field.','field.').replace(f'PRVEq.AspisV8R19.{m}FieldSlice.',f'PRVEq.AspisV8R19.{m}FieldSlice_j1.').replace(f'PRVFresh_AspisV8R19_{m}FieldSlice',f'PRVFresh_AspisV8R19_{m}FieldSlice_j1')
    fn=f'PRVEq_AspisV8R19_{m}FieldSlice_j1.lean';new=open(fn).read()
    pat=re.compile(r'set_option maxHeartbeats 200000 in\ntheorem PRVEq\.AspisV8R19\.'+m+r'FieldSlice_j1\.field\.M31\.mul :.*?#print axioms PRVEq\.AspisV8R19\.'+m+r'FieldSlice_j1\.field\.M31\.mul',re.S)
    assert len(pat.findall(new))==1,m
    new=pat.sub(lambda _:blk,new)
    open(fn,'w').write(new);print(m,'patched')
