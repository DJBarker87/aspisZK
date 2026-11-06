import NKI_BindingPacket
import NJX_AppendDomains
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_AppendPacket
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open NJX_DigestCohort (O D dc)
abbrev State := Fin 4 → NQ
def emptySide (index : U64) (level : Usize) : Bool := decide ((index.val/2^level.val)%2=0)
def start (side : Bool) : Usize := if side then 8#usize else 0#usize
theorem start_bound (side : Bool) : (start side).val+8≤16 := by cases side <;> decide
def carrier (side : Bool) (out : Fin 2 → NQ) : State :=
 if side then ![out 0,out 1,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO]
 else ![FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,out 0,out 1]
def cohort (index : U64) (level : Usize) (frontier : D) (o : O) (high : NQ) : Result State := do
 let side:=emptySide index level
 let d ← if side then FIq_Native.pool_v1.pair_forest_semantic_terminal.empty_root level else ok frontier
 let out ← NKI_DigestPacked.cohort high o d (start side) side
 ok (carrier side out)
structure Packet (index : U64) (level : Usize) (frontier : D) (o : O) (high : NQ) where
 expected : D
 expected_call : (if emptySide index level then FIq_Native.pool_v1.pair_forest_semantic_terminal.empty_root level else ok frontier)=ok expected
 expected_canonical : dc expected
 targets : NKI_DigestTargets.Packet expected (emptySide index level)
 arithmetic : NJX_DigestPacket.Packet high (NKI_DigestView.opened o (start (emptySide index level)) (start_bound _)) (NKI_DigestTargets.cells targets)
 call : NJX_DigestPacket.reference high (NKI_DigestView.opened o (start (emptySide index level)) (start_bound _)) (NKI_DigestTargets.cells targets)=ok arithmetic.out
 association : NKI_DigestPacked.cohort high o expected (start (emptySide index level)) (emptySide index level)=ok arithmetic.out

def output {index level frontier o high} (p : Packet index level frontier o high) : State := carrier (emptySide index level) p.arithmetic.out

theorem canonical {index level frontier o high} (p : Packet index level frontier o high) : ∀ j,Canon (output p j) := by
 intro j
 unfold output carrier
 split <;> fin_cases j <;> first|exact p.arithmetic.out_canonical _|exact FIv_NativeValue.zero.1
/-- Complete branch-dependent arithmetic carrier, SAME expected/offset/high;
full native cut log association follows in its own small module. -/
theorem source (index : U64) (level : Usize) (frontier : D) (o : O) (high : NQ)
 (hl : level.val<20) (hf : dc frontier) (ho : FIw_ArrayValue.canonical o) (hh : Canon high) :
 ∃ p : Packet index level frontier o high,cohort index level frontier o high=ok (output p) := by
 have child : ∃ d,(if emptySide index level then FIq_Native.pool_v1.pair_forest_semantic_terminal.empty_root level else ok frontier)=ok d ∧ dc d := by
  split
  · apply WP.spec_imp_exists
    apply JGa_EmptyRoot.source
    omega
  · exact ⟨frontier,rfl,hf⟩
 obtain ⟨d,cd,hd⟩ := child
 obtain ⟨t,p,cp,co⟩ := NKI_BindingPacket.source high o d (start (emptySide index level)) (emptySide index level) (start_bound _) hh ho hd
 let packet : Packet index level frontier o high := ⟨d,cd,hd,t,p,cp,co⟩
 exact ⟨packet,by simp only [cohort,cd,co,bind_tc_ok];rfl⟩
#print source
#print axioms start_bound
#print axioms canonical
#print axioms source
end AspisR1.NKI_AppendPacket
end
