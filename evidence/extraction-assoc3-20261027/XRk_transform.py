"""Deterministic name/signature adapters only; no extraction, no logic rewrites."""
from pathlib import Path
import hashlib,re,json
E=Path(__file__).resolve().parent
P=Path('evidence/extraction-assoc2-20261027/XRj_L013/sources/XRj_generated/XRh_Release/Funs.lean')
raw=P.read_text();s=raw.replace('XRh_Release.Types','XRk_Types').replace('XRh_Release.FunsExternal','XRk_TerminalModel').replace('XRh_Release','XRk_Release')
renamed=s
# Only call/field references at the incompatible ABI sites change.
s=s.replace('next := core.slice.iter.IteratorIterMut.next','next := XRk_next')
s=s.replace('''step_by :=
    core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.step_by''','''step_by :=
    core.iter.traits.iterator.Iterator.step_by.default''',1)
s=s.replace('''enumerate :=
    core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.enumerate''','''enumerate :=
    core.iter.traits.iterator.Iterator.enumerate.default''',1)
s=s.replace('''next_back :=
    core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT.next_back''','''next_back := XRk_nextBackPair''',1)
s=s.replace('core.iter.adapters.enumerate.IteratorEnumerate.next','XRk_enumerateNext')
# Only the mutable-reverse call: the other occurrence is a shared iterator.
s=s.replace('''core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.slice.iter.IterMut''','''XRk_reverseNext
      (core.slice.iter.IterMut''')
s=s.replace('MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter','XRk_intoIter')
a='sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU32.call_once'
s=s.replace('''call_once :=
    '''+a,'''call_once := fun c i => do
    let (v, _) ← '''+a+''' c i
    ok v''',1)
a='sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut'
s=s.replace('''call_mut :=
    '''+a,'''call_mut := fun c i => do
    let (v, c, restore) ← '''+a+''' c i
    ok (v, restore c)''',1)
s=s.replace('''core.array.from_fn 8#usize
      sampler.low_base_p_digits.closure_1''','''XRk_fromFnState 8#usize
      sampler.low_base_p_digits.closure_1''')
# Qualify compact references. Preserve declaration names, comments and strings.
lines=s.splitlines(keepends=True);in_comment=False
for i,line in enumerate(lines):
 if line.lstrip().startswith('/--'):in_comment=True
 if in_comment:
  if '-/' in line:in_comment=False
  continue
 if line.lstrip().startswith(('--','"','@[','def compact.')):continue
 lines[i]=re.sub(r'(?<![\w.])compact\.',r'_root_.XRk_Release.compact.',line)
s=''.join(lines)
s=s.replace('_root_.XRk_Release.compact.check_values','_root_.compact.check_values')
s=s.replace('_root_.XRk_Release.compact.expand_values','_root_.compact.expand_values')
s=s.replace('core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.rev','XRk_revRestored')
a=s.index('def verifier.BatchedWeights.finish\n'); b=s.index('/--',a)
s=s[:a]+s[a:b].replace('core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.enumerate','XRk_enumerateRestored')+s[b:]

# Record changed declaration blocks against namespace-renamed input, including
# their full before/after text. Input/output bytes pinned independently.
def declarations(x):
 starts=list(re.finditer(r'^def\s+([\w.]+)',x,re.M));out={}
 for i,m in enumerate(starts):
  end=starts[i+1].start() if i+1<len(starts) else x.rfind('end XRk_Release')
  body=x[m.start():end]
  body=body.split('\n/--',1)[0].strip()
  out[m[1]]=body
 return out
before=declarations(renamed);after=declarations(s)
changes=[dict(name=n,before=before[n],after=t,argument='Only qualified names or explicit ABI packing/unpacking change; original computation remains in the referenced declaration. P6 remains OPEN.') for n,t in after.items() if t!=before[n]]
(E/'XRk_Funs.lean').write_text(s)
(E/'XRk_adapter_changes.json').write_text(json.dumps(dict(input=str(P),input_sha256=hashlib.sha256(raw.encode()).hexdigest(),output_sha256=hashlib.sha256(s.encode()).hexdigest(),namespace_renaming='XRh_Release to XRk_Release; imports to XRk_ modules',changes=changes),indent=2)+'\n')
print(len(changes),'changed declarations')
