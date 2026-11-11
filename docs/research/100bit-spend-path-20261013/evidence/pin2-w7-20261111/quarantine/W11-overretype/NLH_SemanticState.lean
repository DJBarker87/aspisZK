import PIN2W11_DropCoe
import NLH_FoldCore
import NLH_ScalarDefs
import NKR_TermSemanticSplitCuts
import NKR_DigestWrapper
set_option autoImplicit false
/-! PIN2 W11 (2026-11-11), NKR batch, PIN2P route (coordinator): `Public` is now the PIN2
`FIw_PublicModel.Public` (W3c `PIN2P.SemanticPublic`) instead of the pre-PIN2 native
`NKI_InitialPrefix.Public`, because this module (or a lemma it uses) applies `ofPublic` to it.
Every pre-PIN2 native read of `p` elaborates through the scoped coercion of `PIN2W11_DropCoe` to
exactly `PIN2P.SemanticPublic.dropDestination p`; where a native clause bundle is destructured,
`pin2_drop` (W3c helper) rewrites its `(dropDestination p).field` projections to `p.field` (rfl).  Statement text is otherwise unchanged; the
digest keys/rows/targets read none of pool, deploymentDomain, destination. -/
noncomputable section
namespace AspisR1.NLH_SemanticState
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open NKI_InitialPrefix (Openings Selectors)
open FIw_PublicModel (Public)
open scoped AspisR1.PIN2W11_DropCoe
open NKR_TermSemanticSource (Packed)
open NKR_TermSemanticCut (Pair)
open pool_v1.pair_forest_semantic_terminal
/-- One complete parent carrier, including unchanged locals between calls.
Native stack layout is not inferred from this value-level SSA carrier. -/
structure State where
 packed : Packed
 digests : Pair
 locals : NLH_ScalarDefs.State
 scalars : Array NQ 2#usize
inductive Event where
 | child (i : Fin 4)
 | digest
 | digestAdd (g : Fin 2)
 | field (i : Fin 12)
 | scalars
 | preweighted
def childCall (pub : Public) (o : Openings) (s : Selectors) (i : Fin 4) (before : Packed) : Result Packed :=
 match i.val with
 | 0 => add_schedule_lanes before pub o s
 | 1 => add_path_lanes before o s
 | 2 => add_value_lanes before o s
 | _ => add_occupancy_lanes before pub o s
/-- Actual child calls at their source arguments. No independently selected
child state or operation dictionary occurs in the parent interpreter. -/
def step (pub : Public) (o : Openings) (s : Selectors) : Event → State → Result State
 | .child i, st => do
   let packed ← childCall pub o s i st.packed
   ok {st with packed := packed}
 | .digest, st => do
   let digests ← NKR_DigestWrapper.reference pub o s
   ok {st with digests := digests}
 | .digestAdd g, st => do
   let slot : Fin 24 := ⟨21+g.val,by omega⟩
   let reply ← field.QM31.add (NJB_ArrayCarrier.cell st.packed slot) (st.digests g)
   ok {st with packed := (NJB_ArrayCarrier.array
     (fun j => if j=slot then reply else NJB_ArrayCarrier.cell st.packed j))}
 | .field i, st => do
   let reply ← NLH_ScalarDefs.call pub o s st.locals i
   ok {st with locals := fun j => if j=i then reply else st.locals j}
 | .scalars, st => do
   let scalars ← scalar_lanes pub.variant (core.option.Option.is_some pub.withdrawal_amount)
     (st.locals 3) (st.locals 5) (st.locals 7) (st.locals 11)
   ok {st with scalars := scalars}
 | .preweighted, st => do
   let packed ← add_preweighted st.packed 92#usize st.scalars
   ok {st with packed := packed}
def order : List Event :=
 (List.finRange 4).map Event.child ++ [.digest,.digestAdd 0,.digestAdd 1] ++
 (List.finRange 12).map Event.field ++ [.scalars,.preweighted]
def run (pub : Public) (o : Openings) (s : Selectors) (st : State) :=
 NLH_FoldCore.run (step pub o s) order st
/-- Exact local no-suffix rule, including the attempted occurrence. -/
theorem aborted (pub : Public) (o : Openings) (s : Selectors)
 (e : Event) (rest : List Event) (st : State) (error : Error)
 (h : step pub o s e st=fail error) :
 NLH_FoldCore.run (step pub o s) (e::rest) st=fail error := by
 simp only [NLH_FoldCore.run,h,bind_tc_fail]
#print axioms aborted
end AspisR1.NLH_SemanticState
end
