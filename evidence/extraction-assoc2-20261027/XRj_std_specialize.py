from pathlib import Path
import re
E=Path(__file__).parent;t=Path('evidence/extraction-assoc1-20261027/XRi_FunsExternal_Template.lean.txt').read_text();f=E/'XRj_FunsExternal.lean';s=f.read_text()
# Template signatures only; no template axiom or attributes are copied.
protos={}
for m in re.finditer(r'\baxiom\s+([\w.]+)',t):
 end=t.find('/--',m.end());end=len(t) if end<0 else end
 protos[m[1]]=re.sub(r'\s+$','',t[m.start():end]).replace('axiom','def',1)
def emit(n,body):
 global s
 if re.search(r'\bdef\s+'+re.escape(n)+r'(?=\s|\{)',s):return
 s+='\n/- Specialization of the pinned Aeneas iterator/default model; original\n signature is the emitted external signature. No result assumption. -/\n'+protos[n]+' :=\n  '+body+'\n'
emit('core.iter.traits.iterator.Iterator.map.default','fun self f => ok ⟨self, f⟩')
emit('core.result.Result.unwrap_or_else','fun self f => match self with\n    | .Ok x => ok x\n    | .Err e => opsfunctionFnOnceFTupleETInst.call_once f e')
for op in ['any','all','fold','collect']:
 n='core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.'+op
 param={'any':'opsfunctionFnMutFTupleABoolInst','all':'opsfunctionFnMutFTupleABoolInst','fold':'opsfunctionFnMutFPairBInst','collect':'traitscollectFromIteratorInst'}[op]
 emit(n,f'core.iter.traits.iterator.Iterator.{op}.default (core.iter.traits.iterator.IteratorRange StepInst) {param}')
for op in ['rev','enumerate','map','step_by']:
 n='core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.'+op
 body={'rev':'core.iter.traits.iterator.Iterator.rev.default','enumerate':'core.iter.traits.iterator.Iterator.enumerate.default','step_by':'core.iter.traits.iterator.Iterator.step_by.default','map':'fun self f => ok ⟨self, f⟩'}[op];emit(n,body)
for op in ['rev','enumerate','map','step_by','collect']:
 n='core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.'+op
 body={'rev':'core.iter.traits.iterator.Iterator.rev.default','enumerate':'core.iter.traits.iterator.Iterator.enumerate.default','step_by':'core.iter.traits.iterator.Iterator.step_by.default','map':'fun self f => ok ⟨self, f⟩','collect':'core.iter.traits.iterator.Iterator.collect.default (core.iter.traits.iterator.IteratorSliceIter T) traitscollectFromIteratorInst'}[op];emit(n,body)
emit('core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.all','core.iter.traits.iterator.Iterator.all.default { next := core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next } opsfunctionFnMutFTupleSharedASliceBoolInst')
f.write_text(s)
