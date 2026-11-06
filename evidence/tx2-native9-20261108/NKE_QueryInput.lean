import NKE_GeometryCuts
import NJJ_Constructors
import NKE_ResumeWidth
set_option autoImplicit false
noncomputable section
namespace NKE_QueryInput
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages
abbrev K := aspis_core.field.QM31
abbrev E := aspis_core.field.wide_exact.WideExact
structure Args where
 proof : Slice U8
 prepared : verifier.Prepared
 accumulator : verifier.Accumulator
 powers : Array E 29#usize
 geometry : verifier.QueryGeometry
 pending : verifier.BatchedWeights

/-- Required payload specification for query-entry windows; NOT a native
certificate (K028–K030 timed out). Physical
allocation, capacity and borrow identity observations are retained in receipts.
Each unselected cell is included by the arbitrary native observation index. -/
structure Cut (before after : Args) : Prop where
 proofSize : after.proof.val.length=57607
 proofCells : ∀ i,i<57607 → after.proof.val[i]?=before.proof.val[i]?
 prepared : NJJ_Constructors.PreparedCut before.prepared after.prepared
 accumulator : NJJ_Constructors.AccumulatorCut before.accumulator after.accumulator
 powers : ∀ i : Fin 29,after.powers.val[i.val]?=before.powers.val[i.val]?
 geometry : NKE_GeometryCuts.Cut before.geometry after.geometry
 rawSize : after.pending.raw.val.length=64
 rawCells : ∀ i,i<64 → after.pending.raw.val[i]?=before.pending.raw.val[i]?
 terms : after.pending.terms=before.pending.terms

theorem same (before after : Args)
 (proofSize : before.proof.val.length=57607)
 (weightSize : before.accumulator.weights.val.length=64)
 (inverseSize : before.geometry.inverses.val.length=12)
 (lineSize : before.geometry.line_z.val.length=12)
 (rawSize : before.pending.raw.val.length=64)
 (cut : Cut before after) : after=before := by
 have proof : after.proof=before.proof := by
  apply Subtype.ext
  apply List.ext_getElem?
  intro i
  by_cases inside : i<57607
  · exact cut.proofCells i inside
  · rw [List.getElem?_eq_none (by rw [cut.proofSize];omega),
     List.getElem?_eq_none (by rw [proofSize];omega)]
 have prepared := NJJ_Constructors.prepared before.prepared after.prepared cut.prepared
 have accumulator := NJJ_Constructors.accumulator before.accumulator after.accumulator
  weightSize cut.accumulator
 have powers := NJJ_Constructors.array_ext after.powers before.powers cut.powers
 have geometry := NKE_GeometryCuts.same before.geometry after.geometry inverseSize lineSize cut.geometry
 have raw : after.pending.raw=before.pending.raw := by
  apply Subtype.ext
  apply List.ext_getElem?
  intro i
  by_cases inside : i<64
  · exact cut.rawCells i inside
  · rw [List.getElem?_eq_none (by rw [cut.rawSize];omega),
     List.getElem?_eq_none (by rw [rawSize];omega)]
 have terms := cut.terms
 have pending : after.pending=before.pending := by
  cases h : after.pending
  cases h1 : before.pending
  simp_all only []
 cases before
 cases after
 simp_all only []

def child (args : Args) := NJJ_Common.query args.proof args.prepared args.accumulator
 args.powers none args.geometry args.pending 22#usize

theorem child_at_same_arguments (before after : Args)
 (proofSize : before.proof.val.length=57607)
 (weightSize : before.accumulator.weights.val.length=64)
 (inverseSize : before.geometry.inverses.val.length=12)
 (lineSize : before.geometry.line_z.val.length=12)
 (rawSize : before.pending.raw.val.length=64)
 (cut : Cut before after) : child after=child before := by
 rw [same before after proofSize weightSize inverseSize lineSize rawSize cut]
#print axioms same
#print axioms child_at_same_arguments
end NKE_QueryInput
