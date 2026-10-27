import Lean
import KSC2_MutConstructors
open Aeneas Aeneas.Std
#print core.iter.traits.iterator.Iterator.collect.default
#print core.iter.traits.iterator.Iterator.rev.default
#print core.iter.traits.iterator.Iterator.enumerate.default
#print core.iter.traits.iterator.Iterator.step_by.default
#print core.slice.iter.IteratorSliceIter.next
#print core.slice.iter.IteratorIterMut.next

open Lean Elab Command
run_cmd do
  let env ← getEnv
  for n in #[`Aeneas.Std.core.iter.traits.iterator.Iterator.any.default,
    `Aeneas.Std.core.iter.traits.iterator.Iterator.all.default,
    `Aeneas.Std.core.iter.traits.iterator.Iterator.fold.default,
    `Aeneas.Std.core.iter.traits.iterator.Iterator.map.default,
    `Aeneas.Std.core.option.Option.ok_or,
    `Aeneas.Std.core.result.Result.unwrap_or_else,
    `Aeneas.Std.core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT.next_back] do
    logInfo m!"KSC2_P7_PRESENT {n}: {env.contains n}"
