import Aeneas
open Aeneas Aeneas.Std Result Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut out : Array String := #[]
  for (n,_) in env.constants.fold (fun a n c => a.push (n,c)) #[] do
    let s := n.toString
    if s.startsWith "Aeneas.Std" && !s.contains "match_" && !s.contains "proof_" && !s.contains "_eq_" && !s.contains "_unfold" && !s.contains "_sunfold" && (s.contains "IntoIter" || s.contains "Zip" || s.contains "ChunksExact" || s.contains ".Rev" || s.contains "adapters.rev" || s.contains "SharedIter" || s.contains "slice.iter" || s.contains "iterator.Iterator.") then
      out := out.push (s.drop 11)
  logInfo (String.intercalate "\n" (out.qsort (· < ·)).toList)
#print core.iter.adapters.zip.Zip
#print core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
#print core.iter.traits.iterator.Iterator.zip.trait_default
#print core.iter.traits.iterator.Iterator.rev.trait_default
#print core.iter.adapters.rev.Rev
#print core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
#print core.slice.iter.ChunksExact
#print core.iter.traits.iterator.IteratorChunksExact
