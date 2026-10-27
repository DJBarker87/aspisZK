import Aeneas
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for n in [`Aeneas.Std.MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter,`Aeneas.Std.Slice.Insts.CoreCmpPartialEqArray.eq,`Aeneas.Std.Slice.Insts.CoreCmpPartialEqArray.ne,`Aeneas.Std.alloc.vec.Vec.is_empty,`Aeneas.Std.core.array.fromFnList,`Aeneas.Std.core.array.from_fn,`Aeneas.Std.core.array.mapListFnMut,`Aeneas.Std.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.collect,`Aeneas.Std.core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.fold,`Aeneas.Std.core.iter.traits.iterator.Iterator.all.default,`Aeneas.Std.core.slice.cmp.PartialEqSlice.eq,`Aeneas.Std.core.slice.cmp.PartialEqSlice.ne,`Aeneas.Std.core.slice.iter.IteratorIterMut.next,`Aeneas.Std.Array.from_slice,`Aeneas.Std.Array.to_slice,`Aeneas.Std.core.iter.traits.iterator.Iterator.collect.default] do
    logInfo m!"P7 availability {n}: {env.contains n}"
