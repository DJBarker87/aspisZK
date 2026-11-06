import NKR_TermScalarCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_TermScalarSplitCuts
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
 ∀ j,j.val<i.val→st j=values p j
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

theorem actual {pub o s before} (p : Packet pub o s before) (i : Fin 12) :
 call pub o s (values p) i=ok (values p i) := by
 fin_cases i
 · exact FIw_ScalarArithmetic.lift_run pub.asset_id
 · exact p.asset_sub
 · exact p.row_calls 0
 · exact p.product_calls 0
 · exact p.row_calls 1
 · exact p.product_calls 1
 · exact p.row_calls 2
 · exact p.product_calls 2
 · exact p.row_calls 3
 · exact FIw_ScalarArithmetic.lift_run (amount pub)
 · exact p.amount_sub
 · exact p.product_calls 3

theorem operands {pub o s before} (p : Packet pub o s before) (st : State) (i : Fin 12)
 (ready : Ready p st i) :
 left pub o st i=left pub o (values p) i ∧ right pub st i=right pub (values p) i := by
 constructor
 · fin_cases i <;> first
    | rfl
    | exact ready 2 (by decide)
    | exact ready 4 (by decide)
    | exact ready 6 (by decide)
    | exact ready 8 (by decide)
 · fin_cases i <;> first
    | rfl
    | exact ready 0 (by decide)
    | exact ready 1 (by decide)
    | exact ready 9 (by decide)
    | exact ready 10 (by decide)

/-- All twelve native pointwise cuts chain along the source result order.
Prior operands come from the preceding snapshot; future SSA slots are not
read and are retained by the frame. Every entered field Result is supplied
by the SAME internally constructed source packet. -/
theorem chain {pub o s before} (p : Packet pub o s before) (i : Fin 12) :
 call pub o s (snapshot p i.val) i=ok (values p i) ∧
 FieldCut pub o s (snapshot p i.val) i (values p i)
  ⟨⟨NKR_TermScalarCut.kinds i,left pub o (snapshot p i.val) i,right pub (snapshot p i.val) i⟩,
    (if (row i).isSome then some s else none),row i,snapshot p (i.val+1),1⟩ := by
 have ready : Ready p (snapshot p i.val) i := by intro j h;exact if_pos h
 have args:=operands p (snapshot p i.val) i ready
 constructor
 · unfold call
   rw [args.1,args.2]
   exact actual p i
 · refine ⟨rfl,rfl,rfl,rfl,?_⟩
   intro j
   by_cases same : j=i
   · subst j
     simp only [snapshot,if_pos (Nat.lt_succ_self i.val),ite_true]
   · have different : j.val≠i.val := by intro h;exact same (Fin.ext h)
     unfold snapshot
     by_cases earlier : j.val<i.val
     · simp only [if_pos earlier,if_neg same,if_pos (show j.val<i.val+1 by omega)]
     · simp only [if_neg earlier,if_neg same,if_neg (show ¬j.val<i.val+1 by omega)]

structure TailObservation where
 variant : pool_v1.pair_forest_semantic_terminal.CompiledVariant
 present : Bool
 args : Fin 4 → NQ
 packedBefore : Packed
 values : Array NQ 2#usize
 after : Packed
 calls : Nat
 start : Nat
def TailCut {pub o s before} (p : Packet pub o s before) (ob : TailObservation) : Prop :=
 ob.variant=pub.variant ∧ ob.present=core.option.Option.is_some pub.withdrawal_amount ∧
 ob.args=p.products ∧ ob.packedBefore=before ∧ ob.values=p.scalars ∧ ob.after=p.out ∧ ob.calls=2 ∧ ob.start=92
theorem tail {pub o s before} (p : Packet pub o s before) :
 TailCut p ⟨pub.variant,core.option.Option.is_some pub.withdrawal_amount,p.products,before,p.scalars,p.out,2,92⟩ :=
 ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
#print axioms actual
#print axioms operands
#print axioms chain
#print axioms tail
end AspisR1.NKR_TermScalarSplitCuts
end
