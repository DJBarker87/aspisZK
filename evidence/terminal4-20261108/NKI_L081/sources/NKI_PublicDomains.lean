import NJX_AppendDomains
import NJX_DigestCohort
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_PublicDomains
open Aeneas Aeneas.Std
open FIv_NativeValue (Canon)
open NJX_DigestCohort (dc)
open NJX_AppendDomains (Frontier)
abbrev Selectors := FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors
def carryLevel (carry : Nat) : Fin 20 := ⟨min carry 19,by have h:=Nat.min_le_right carry 19;omega⟩
def high (s : Selectors) (carry : Nat) :=
 NJB_ArrayCarrier.cell s.high ⟨33+(carryLevel carry).val,by have h:=(carryLevel carry).isLt;scalar_tac⟩
def lows : Fin 3 → Fin (16#usize).val := ![⟨0,by decide⟩,⟨11,by decide⟩,⟨12,by decide⟩]
def highs : Fin 4 → Fin (64#usize).val := ![⟨56,by decide⟩,⟨26,by decide⟩,⟨32,by decide⟩,⟨53,by decide⟩]
/--251actual carry=min(carry,19), high33+index, next_frontier[index],
all3low inputs and4ordinary high inputs. No count1or carry<20restriction. -/
theorem source (s : Selectors) (f : Frontier) (carry : Nat)
 (hh : FIw_ArrayValue.canonical s.high) (hl : FIw_ArrayValue.canonical s.low) (hf : ∀ d∈f.val,dc d) :
 (carryLevel carry).val=min carry 19 ∧ dc (NJX_AppendDomains.frontier f (carryLevel carry)) ∧
 Canon (high s carry) ∧ (∀ g,Canon (NJB_ArrayCarrier.cell s.low (lows g))) ∧
 ∀ g,Canon (NJB_ArrayCarrier.cell s.high (highs g)) := by
 exact ⟨rfl,hf _ (List.getElem_mem _),NJB_ArrayCarrier.canonical_cell _ hh _,
  fun g=>NJB_ArrayCarrier.canonical_cell _ hl _,fun g=>NJB_ArrayCarrier.canonical_cell _ hh _⟩
#print axioms source
end AspisR1.NKI_PublicDomains
end
