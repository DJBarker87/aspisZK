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
def values {pub o s before} (p : Packet pub o s before) : State :=
 ![FIw_ScalarArithmetic.lifted pub.asset_id,p.difference,p.selected 0,p.products 0,
 p.selected 1,p.products 1,p.selected 2,p.products 2,p.selected 3,
 FIw_ScalarArithmetic.lifted (amount pub),p.withdrawalDifference,p.products 3]
def snapshot {pub o s before} (p : Packet pub o s before) (n : Nat) : State :=
 fun j=>if j.val<n then values p j else field.QM31.ZERO
def Ready {pub o s before} (p : Packet pub o s before) (st : State) (i : Fin 12) : Prop :=
 ∀ j : Fin 12,j.val<i.val→st j=values p j
def left (pub : Public) (o : Openings) (st : State) : Fin 12 → NQ :=
 ![FIw_ScalarArithmetic.lifted pub.asset_id,NJB_ArrayCarrier.cell o.z ⟨1,by decide⟩,field.QM31.ZERO,st 2,
 field.QM31.ZERO,st 4,field.QM31.ZERO,st 6,field.QM31.ZERO,FIw_ScalarArithmetic.lifted (amount pub),
 NJB_ArrayCarrier.cell o.z ⟨10,by decide⟩,st 8]
def right (pub : Public) (st : State) : Fin 12 → NQ :=
 ![field.QM31.ZERO,st 0,field.QM31.ZERO,st 1,field.QM31.ZERO,st 1,field.QM31.ZERO,st 1,
 field.QM31.ZERO,field.QM31.ZERO,st 9,st 10]
def operation (pub : Public) (s : Selectors) : Fin 12 → NQ → NQ → Result NQ :=
 ![(fun _ _=>pool_v1.pair_forest_semantic_terminal.lift_m31 pub.asset_id),field.QM31.sub,
 (fun _ _=>s.row 44#usize),field.QM31.mul,(fun _ _=>s.row 508#usize),field.QM31.mul,
 (fun _ _=>s.row 460#usize),field.QM31.mul,(fun _ _=>s.row 1010#usize),
 (fun _ _=>pool_v1.pair_forest_semantic_terminal.lift_m31 (amount pub)),field.QM31.sub,field.QM31.mul]
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
