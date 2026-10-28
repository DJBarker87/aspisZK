import R1Z.PV_DL_CompressionTrace
open Aeneas Aeneas.Std Result
namespace R1Z.PV_DL_BatchPlan
set_option autoImplicit false

/-- Contiguous bulk region, with the call boundary preserved. This uses the
same take/drop quotient specification as V233; source association is separate. -/
def bulk (input : List U8) : List U8 × List U8 :=
  let consumed := (input.length/64)*64
  (input.take consumed,input.drop consumed)

theorem reassemble (input : List U8) : (bulk input).1++(bulk input).2=input := by
  exact List.take_append_drop _ _

theorem remainder (input : List U8) : (bulk input).2.length<64 := by
  simp only [bulk,List.length_drop]
  have h := Nat.mod_lt input.length (by decide : 0<64)
  have e := Nat.mod_add_div input.length 64
  omega

def events (input : List U8) : List (List U8) :=
  if (bulk input).1=[] then [] else [(bulk input).1]

def run {S : Type} (compress : S → List U8 → Result S)
    (state : S) (input : List U8) : Result S :=
  PV_DL_CompressionTrace.run compress (events input) state

theorem no_bulk {S : Type} (compress : S → List U8 → Result S)
    (state : S) (input : List U8) (h : (bulk input).1=[]) :
    run compress state input=ok state := by
  simp only [run,events,h,if_true,PV_DL_CompressionTrace.run]

theorem single_bulk {S : Type} (compress : S → List U8 → Result S)
    (state : S) (input : List U8) (h : (bulk input).1≠[]) :
    run compress state input=compress state (bulk input).1 := by
  simp only [run,events,if_neg h,PV_DL_CompressionTrace.run,bind_tc_ok]
  cases compress state (bulk input).1 <;> rfl

#print axioms bulk
#print axioms reassemble
#print axioms remainder
#print axioms events
#print axioms run
#print axioms no_bulk
#print axioms single_bulk
end R1Z.PV_DL_BatchPlan
