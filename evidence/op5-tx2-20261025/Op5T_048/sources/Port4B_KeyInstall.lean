import Port4B_BatchJoin

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_KeyInstall
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable

def queries (raw : Array U32 22#usize) : Fin 22 → Fin 262144 := fun j =>
  ⟨((raw.val.map UScalar.val)[j.val]?.getD 0)%262144,Nat.mod_lt _ (by decide)⟩

def prefixKeys (raw : Array U32 22#usize) (batch kind : Nat) : List U64 :=
  (OraclePortSelectedDraft.batchPositions batch).map (MultiproofConeSortOrder.packed (queries raw) batch kind)

theorem prefix_bound (raw : Array U32 22#usize) (batch kind : Nat) : (prefixKeys raw batch kind).length≤16 := by
  simp only [prefixKeys,List.length_map,OraclePortSelectedDraft.batchPositions]
  split <;> simp

def keyArray (raw : Array U32 22#usize) (batch kind : Nat) : Array U64 16#usize :=
  ⟨prefixKeys raw batch kind++List.replicate (16-(prefixKeys raw batch kind).length) 0#u64,by
    have bound := prefix_bound raw batch kind
    simp only [List.length_append,List.length_replicate]
    change (prefixKeys raw batch kind).length+(16-(prefixKeys raw batch kind).length)=16
    omega⟩

/-- P6 reached canonical key lowering, using the independently certified
packed-key cells. Non-admitted arguments retain an explicit failure; this
is NOT a new extraction or a total equality claim for arbitrary native keys. -/
def build (raw : Array U32 22#usize) (lo n kind : Usize) : Result (Array U64 16#usize) :=
  let b := if lo=0#usize then 0 else 1
  if admitted : n.val=(OraclePortSelectedDraft.batchPositions b).length ∧
      (lo=0#usize ∨ lo=10#usize) ∧ kind.val<3
  then ok (keyArray raw b kind.val) else fail .panic

def install (base : Port3_NativeBatchBody.Ops) : Port3_NativeBatchBody.Ops := {base with op4:=build}

/-- Saved/prepared body provenance discharges CANONICAL query binding, before
using the owned key lowering; modulo is not a weakening of source raw words. -/
theorem queries_bound (p : AspisR1Stage2.verifier.Prepared) (a : AspisR1Stage2.verifier.Accumulator)
    (pm : OraclePortCheckpointAbiC5.Prepared)
    (am : QueryAccumulator.State OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E)
    (fields : CheckpointBytes4SavedFields.BodyMatches p a pm am) : queries p.queries=pm.queries := by
  funext j
  apply Fin.ext
  simp only [queries,fields.queries,List.getElem?_ofFn,j.isLt,↓reduceDIte,Option.getD_some,
    Nat.mod_eq_of_lt (pm.queries j).isLt]

/-- Discharges PackedKeys for this explicit owned key installation, from
canonical physical-query binding only. Source/Kani lowering adoption remains P6. -/
theorem packed (base : Port3_NativeBatchBody.Ops) (raw : Array U32 22#usize)
    (q : Fin 22 → Fin 262144) (binding : queries raw=q) (batch kind : Usize)
    (hb : batch.val<2) (hk : kind.val<3) :
    Port4B_TreeJoin.PackedKeys (install base) raw q batch kind := by
  intro returned call
  have sizes := Port4B_Bounds.count batch
  by_cases zero : batch=0#usize
  · subst batch
    change build raw 0#usize (Port4B_TreeCuts.count 0#usize) kind=ok returned at call
    have nvalue : (Port4B_TreeCuts.count 0#usize).val=10 := sizes.1
    simp only [build,if_pos rfl,OraclePortSelectedDraft.batchPositions,List.length_range,nvalue,
      eq_self_iff_true,true_or,true_and,hk,↓reduceDIte] at call
    have same := Result.ok.inj call
    subst returned
    simp only [keyArray,nvalue,prefixKeys,binding]
    simp [OraclePortSelectedDraft.batchPositions]
  · have nonzero : batch.val≠0 := by intro h;exact zero (UScalar.eq_of_val_eq h)
    have value : batch.val=1 := by omega
    have nvalue : (Port4B_TreeCuts.count batch).val=12 := by simpa only [if_neg zero] using sizes.1
    change build raw (Port4B_TreeCuts.lo batch) (Port4B_TreeCuts.count batch) kind=ok returned at call
    simp only [build,Port4B_TreeCuts.lo,if_neg zero,show ¬10#usize=0#usize by decide,
      if_false,OraclePortSelectedDraft.batchPositions,show ¬(1:Nat)=0 by decide,if_false,
      List.length_map,List.length_range,nvalue,eq_self_iff_true,or_true,true_and,hk,↓reduceDIte] at call
    have same := Result.ok.inj call
    subst returned
    simp only [keyArray,nvalue,prefixKeys,binding,value]
    simp [OraclePortSelectedDraft.batchPositions]

#print axioms prefix_bound
#print axioms queries_bound
#print axioms packed
end AspisR1.Port4B_KeyInstall
end
