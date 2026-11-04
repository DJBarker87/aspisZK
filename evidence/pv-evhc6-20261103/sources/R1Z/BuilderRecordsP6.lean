import R1Z.BuilderRecordsReference
import R1Z.BuilderBankExtracted

/-! P6 composition boundary. `FieldsEqual` is the proposition certified by
D90's six Kani projections. It is a named hypothesis, never a Lean axiom.
The checked reference computation then transports all bank outputs, including
failure/divergence and the merge flag, through the axiom-free std models.
This is record-substitution equality, not yet Parts-to-copyCell refinement. -/
set_option autoImplicit false
namespace R1Z.BuilderRecordsP6
open Aeneas Aeneas.Std Result AspisBuilderRecordsReference
open pool_v1.pair_forest_copy_builder BuilderRecordsReference

structure FieldsEqual (w : RW) (p : RP) (v : RW) (q : RP) : Prop where
  input_value : w.input_value = v.input_value
  output_value : w.output_value = v.output_value
  change_value : w.change_value = v.change_value
  sk : w.sk = v.sk
  salt : w.salt = v.salt
  bits : w.bits = v.bits
  sibs : w.sibs = v.sibs
  pair_first : w.pair_first = v.pair_first
  pair_occupied : w.pair_occupied = v.pair_occupied
  pair_second : w.pair_second = v.pair_second
  pair_inverse : w.pair_inverse = v.pair_inverse
  recipient_owner : w.recipient_owner = v.recipient_owner
  recipient_salt : w.recipient_salt = v.recipient_salt
  change_owner : w.change_owner = v.change_owner
  change_salt : w.change_salt = v.change_salt
  transfer : p.transfer = q.transfer
  asset : p.asset = q.asset
  next_pair_index : p.next_pair_index = q.next_pair_index
  frontier : p.frontier = q.frontier
  empty : p.empty = q.empty

theorem FieldsEqual.eq {w v : RW} {p q : RP} (e : FieldsEqual w p v q) :
    w = v ∧ p = q := by
  constructor
  · cases w; cases v
    cases e
    congr <;> assumption
  · cases p; cases q
    cases e
    congr <;> assumption

/-- The exact P6 route combines a successful extracted reference execution
with D90's pointwise equality certificate. No proof of source admission is
encoded here. The root table is shared by both sides, as in D90. -/
def Route (w : RW) (p : RP) (input : Input) (out : U32) (rec : Option Note)
    (chg : Note) (s : Snapshot) (asset : U32) (empty : Roots) : Prop :=
  ∃ v q, records_reference.records_reference_with_roots input out rec chg s asset empty =
    ok (v,q) ∧ FieldsEqual w p v q

theorem route_records {w : RW} {p : RP} {input : Input} {out : U32} {rec : Option Note}
    {chg : Note} {s : Snapshot} {asset : U32} {empty : Roots}
    (p6 : Route w p input out rec chg s asset empty) :
    w = witness input out rec chg ∧ p = publicRecord rec s asset empty := by
  obtain ⟨v, q, h, eq⟩ := p6
  rw [BuilderRecordsReference.records] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok.inj h)
  exact eq.eq

abbrev BankRW := AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder.RW
abbrev BankRP := AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder.RP

def bankWitness (w : RW) : BankRW where
  input_value := w.input_value
  output_value := w.output_value
  change_value := w.change_value
  sk := w.sk
  salt := w.salt
  bits := w.bits
  sibs := w.sibs
  pair_first := w.pair_first
  pair_occupied := w.pair_occupied
  pair_second := w.pair_second
  pair_inverse := w.pair_inverse
  recipient_owner := w.recipient_owner
  recipient_salt := w.recipient_salt
  change_owner := w.change_owner
  change_salt := w.change_salt

def bankPublic (p : RP) : BankRP where
  transfer := p.transfer
  asset := p.asset
  next_pair_index := p.next_pair_index
  frontier := p.frontier
  empty := p.empty

/-- Equality of the entire extracted bank computation with the approved std
models: stable, late, merged and merge-check flag, not just selected cells.
It does not assert equality of either side with copyCellMerged. -/
theorem route_banks {w : RW} {p : RP} {input : Input} {out : U32} {rec : Option Note}
    {chg : Note} {s : Snapshot} {asset : U32} {empty : Roots}
    (p6 : Route w p input out rec chg s asset empty) :
    AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder.merged_banks
      (bankWitness w) (bankPublic p) =
    AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder.merged_banks
      (bankWitness (witness input out rec chg)) (bankPublic (publicRecord rec s asset empty)) := by
  obtain ⟨hw, hp⟩ := route_records p6
  rw [hw, hp]

#print axioms FieldsEqual.eq
#print axioms route_records
#print axioms route_banks
end R1Z.BuilderRecordsP6
