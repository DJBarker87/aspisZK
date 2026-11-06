import NKR_TermScalarCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_ScalarDefs
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open NKI_InitialPrefix (Public Openings Selectors)
open NKR_TermScalarInvocation (Packet Packed amount)
open NKI_AppendCut (Event)
abbrev State := Fin 12 → NQ
def values {pub o s before} (p : Packet pub o s before) (i : Fin 12) : NQ :=
 match i.val with
 | 0 => FIw_ScalarArithmetic.lifted pub.asset_id
 | 1 => p.difference
 | 2 => p.selected 0
 | 3 => p.products 0
 | 4 => p.selected 1
 | 5 => p.products 1
 | 6 => p.selected 2
 | 7 => p.products 2
 | 8 => p.selected 3
 | 9 => FIw_ScalarArithmetic.lifted (amount pub)
 | 10 => p.withdrawalDifference
 | _ => p.products 3
def snapshot {pub o s before} (p : Packet pub o s before) (n : Nat) : State :=
 fun j=>if j.val<n then values p j else field.QM31.ZERO
def Ready {pub o s before} (p : Packet pub o s before) (st : State) (i : Fin 12) : Prop :=
 ∀ j : Fin 12,j.val < i.val → st j = values p j
def left (pub : Public) (o : Openings) (st : State) (i : Fin 12) : NQ :=
 match i.val with
 | 0 => FIw_ScalarArithmetic.lifted pub.asset_id
 | 1 => NJB_ArrayCarrier.cell o.z ⟨1,by decide⟩
 | 3 => st 2
 | 5 => st 4
 | 7 => st 6
 | 9 => FIw_ScalarArithmetic.lifted (amount pub)
 | 10 => NJB_ArrayCarrier.cell o.z ⟨10,by decide⟩
 | 11 => st 8
 | _ => field.QM31.ZERO
def right (pub : Public) (st : State) (i : Fin 12) : NQ :=
 match i.val with
 | 1 => st 0
 | 3 | 5 | 7 => st 1
 | 10 => st 9
 | 11 => st 10
 | _ => field.QM31.ZERO
def operation (pub : Public) (s : Selectors) (i : Fin 12) : NQ → NQ → Result NQ :=
 match i.val with
 | 0 => fun _ _ => pool_v1.pair_forest_semantic_terminal.lift_m31 pub.asset_id
 | 1 | 10 => field.QM31.sub
 | 2 => fun _ _ => s.row 44#usize
 | 4 => fun _ _ => s.row 508#usize
 | 6 => fun _ _ => s.row 460#usize
 | 8 => fun _ _ => s.row 1010#usize
 | 9 => fun _ _ => pool_v1.pair_forest_semantic_terminal.lift_m31 (amount pub)
 | _ => field.QM31.mul
def call (pub : Public) (o : Openings) (s : Selectors) (st : State) (i : Fin 12) :=
 operation pub s i (left pub o st i) (right pub st i)
def row : Fin 12 → Option Usize :=
 ![none,none,some 44#usize,none,some 508#usize,none,some 460#usize,none,some 1010#usize,none,none,none]
structure FieldObservation where
 event : Event
 selectors : Option Selectors
 row : Option Usize
 after : State
 calls : Nat
/-- Native one-statement Result at arbitrary twelve-value prestate, including
the full pointwise frame. The value carrier is source SSA context, not an
assertion about the layout or uninitialized cells of a Rust stack frame. -/
def FieldCut (pub : Public) (o : Openings) (s : Selectors) (st : State) (i : Fin 12)
 (reply : NQ) (ob : FieldObservation) : Prop :=
 ob.event=⟨NKR_TermScalarCut.kinds i,left pub o st i,right pub st i⟩ ∧
 ob.selectors=(if (row i).isSome then some s else none) ∧ ob.row=row i ∧
 ob.calls=1 ∧ ∀ j,ob.after j=if j=i then reply else st j

end AspisR1.NLH_ScalarDefs
end
