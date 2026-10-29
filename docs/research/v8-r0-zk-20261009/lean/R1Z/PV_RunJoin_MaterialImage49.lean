import R1Z.PV_RunJoin_MaterialVec49
import R1Z.PV_RunJoin_SourceArray44
import R1Z.PV_RunJoin_FoldCell44
set_option autoImplicit false
namespace R1Z.PV_RunJoin_MaterialImage49
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitWideOps48 ProverCommitMix48

theorem complete (w : Nat → Raw) :
    alloc.vec.Vec.deref (PV_RunJoin_MaterialVec49.vec (sourceArray 1024#usize w))=
      Array.to_slice (PV_RunJoin_FoldCell44.array 1024#usize w) := by
  apply Subtype.ext
  change (List.ofFn (fun i : Fin 1024 => source (w i.val))).map ProverRwDictionaryTower.fromW=
    List.ofFn (fun i : Fin 1024 => ProverRwDictionaryTower.fromW (source (w i.val)))
  simp only [List.map_ofFn,Function.comp_def]
#print axioms complete
end R1Z.PV_RunJoin_MaterialImage49
