import NKI_SharedScaling
import NKI_ValueFactor
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_ValueFinish
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open NKI_ValuePrefix (Openings Selectors)
def conservation (packed : Array NQ 24#usize) (o : Openings) (s : Selectors) : Result (Array NQ 24#usize) := do
  let i2 ← 16#usize * VALUE_AUXILIARY_BLOCK
  let i3 ← i2 + 6#usize
  let conservation_selector ← pool_v1.pair_forest_copy_terminal.Selectors.row s i3
  let q15 ← Array.index_usize o.z 0#usize
  let q16 ← Array.index_usize o.z 1#usize
  let q17 ← field.QM31.sub q15 q16
  let q18 ← Array.index_usize o.z 2#usize
  let q19 ← field.QM31.sub q17 q18
  let q20 ← field.QM31.mul conservation_selector q19
  let q21 ← Array.index_usize o.succ_z 0#usize
  let q22 ← Array.index_usize o.succ_z 1#usize
  let q23 ← field.QM31.sub q21 q22
  let q24 ← field.QM31.mul conservation_selector q23
  add_preweighted packed 82#usize (Array.make 2#usize [q20,q24])
def scaled (packed : Array NQ 24#usize) (range : Array NQ 33#usize) (selector : NQ) : Result (Array NQ 24#usize) := do
 let weighted←FIy_ScaleReadback.run range selector
 pool_v1.pair_forest_semantic_terminal.add_preweighted packed 49#usize weighted

def reference (packed : Array NQ 24#usize) (o : Openings) (s : Selectors) (range : Array NQ 33#usize) (selector : NQ) : Result (Array NQ 24#usize) := do
 let middle←NJL_SharedRoot.reference packed range selector
 conservation middle o s

theorem factor (packed : Array NQ 24#usize) (o : Openings) (s : Selectors) (range : Array NQ 33#usize) (selector : NQ) :
 JGa_ValueFinish.run packed o s range selector=(do let middle←scaled packed range selector;conservation middle o s) := by
 simp only [JGa_ValueFinish.run,scaled,conservation,FIy_ScaleReadback.run,Aeneas.Std.uncurry,bind_assoc_eq,bind_tc_ok]
 congr 1

theorem association (packed : Array NQ 24#usize) (o : Openings) (s : Selectors) (range : Array NQ 33#usize) (selector : NQ)
 (hp : canonical packed) (hr : canonical range) (hs : Canon selector) :
 reference packed o s range selector=JGa_ValueFinish.run packed o s range selector := by
 rw [factor]
 unfold reference scaled
 rw [NKI_SharedScaling.source packed range selector hp hr hs]

@[step] theorem conservation_source (packed : Array NQ 24#usize) (o : Openings) (s : Selectors)
 (hp : canonical packed) (hz : canonical o.z) (hs : canonical o.succ_z)
 (hh : canonical s.high) (hl : canonical s.low) :
 conservation packed o s ⦃ out=>canonical out ⦄ := by
 unfold conservation pool_v1.pair_forest_semantic_terminal.VALUE_AUXILIARY_BLOCK
 step*
 all_goals first | assumption | scalar_tac | (intro x hx;simp only [Array.make,List.mem_cons,List.not_mem_nil,or_false] at hx;rcases hx with rfl|rfl <;> assumption)
#print axioms factor
#print axioms association
#print axioms conservation_source
end AspisR1.NKI_ValueFinish
end
