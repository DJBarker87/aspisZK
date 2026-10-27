from pathlib import Path
import re,json,hashlib
E=Path(__file__).parent
base='aeneas-verif/v7-tag73-current-caller-source-20260830/proof/V7Tag73CurrentHelpersOpaque/FunsExternalBase.lean'
codec='aeneas-verif/v7-registry-v2-production-call-composition-20260831/generated/V7PairForestProductionCodecs/FunsExternal.lean'
sel='aeneas-verif/v7-tag73-selected-pool-callers-current/generated/V7Tag73SelectedSemanticLoopForm/FunsExternal.lean'
merkle='aeneas-verif/v7-merkle-k12-accepted-source-20260825/caller/generated/V7MerkleCaller/FunsExternal.lean'
rows=[]; parts=['import Aeneas\nimport XRh_Release.Types\nopen Aeneas Aeneas.Std Result ControlFlow Error\nopen XRh_Release\nset_option linter.dupNamespace false\n']
def take(path,name):
 s=Path(path).read_text();m=re.search(r'^def\s+'+re.escape(name)+r'(?=\s|\{)',s,re.M)
 assert m,(path,name)
 end=re.search(r'\n(?=/--|@\[|def |end |namespace |/-!)',s[m.end():]);j=m.end()+end.start() if end else len(s)
 body=s[m.start():j].strip()
 parts.append('/- Reused definition: '+path+':'+str(s[:m.start()].count('\n')+1)+' -/\n'+body+'\n')
 rows.append(dict(name=name,path=path,line=s[:m.start()].count('\n')+1,source_sha256=hashlib.sha256(s.encode()).hexdigest()))
for n in ['core.iter.traits.iterator.Iterator.any.default','core.iter.traits.iterator.Iterator.all.default']:take(codec,n)
for n in ['core.iter.traits.iterator.Iterator.fold.default','core.array.fromFnList','core.array.from_fn','core.array.mapListFnMut','core.array.Array.map','MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter','core.option.Option.ok_or','core.slice.iter.Windows.windowAt','core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next','core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back','core.slice.Slice.windows','alloc.vec.Vec.is_empty']:take(base,n)
take(codec,'Slice.Insts.CoreCmpPartialEqArray.eq')
# ne implemented by the same trait eq + Boolean negation, as the existing models do.
parts.append('''def Slice.Insts.CoreCmpPartialEqArray.ne {T U : Type} {N : Usize}
    (eq : core.cmp.PartialEq T U) (a : Slice T) (b : Array U N) : Result Bool := do
  let same ← Slice.Insts.CoreCmpPartialEqArray.eq eq a b
  ok (!same)
''')
for n in ['core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any','core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all']:take(codec,n)
for n in ['core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.fold','core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.any','core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.fold']:take(base,n)
take(sel,'core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.fold')
(E/'XRj_FunsExternal.lean').write_text('\n'.join(parts))
(E/'XRj_reused_definitions.json').write_text(json.dumps(rows,indent=2)+'\n')
