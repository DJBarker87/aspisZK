import PV_B3P_PrefixTypes224
import R1Z.ProverRwFullTypes
namespace PV_B3P_HelperView224
open Aeneas Aeneas.Std
set_option autoImplicit false

def probe {α : Type} (xs : List α) : Array (Option α) 1024#usize :=
  ⟨List.ofFn (fun i : Fin 1024 => xs[i.val]?),by simp only [List.length_ofFn]; rfl⟩

def columns (xs : Array (alloc.vec.Vec U32) 16#usize) : Array (Array (Option U32) 1024#usize) 16#usize :=
  ⟨List.ofFn (fun i : Fin 16 => probe (xs.val[i.val]'(by have h := xs.property; scalar_tac)).val),
    by simp only [List.length_ofFn]; rfl⟩

def fromTrace (trace : ProverRwFull.aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1) :
    PV_B3P_224Prefix.prefix224.View :=
  { stable := columns trace.stable.c1
    late := columns trace.late
    withdrawal := match trace.variant with
      | .PrivateTransfer => false
      | .Withdrawal => true }

theorem probe_value {α : Type} (xs : List α) (r : Nat) (hr : r < 1024) :
    (probe xs).val[r]'(by have h := (probe xs).property; scalar_tac) = xs[r]? := by
  simp only [probe,List.getElem_ofFn]

theorem column_value (xs : Array (alloc.vec.Vec U32) 16#usize) (c : Nat) (hc : c < 16) :
    (columns xs).val[c]'(by have h := (columns xs).property; scalar_tac) =
      probe (xs.val[c]'(by have h := xs.property; scalar_tac)).val := by
  simp only [columns,List.getElem_ofFn]

-- Missing source vector cells remain None. The view does not silently pad
-- malformed short vectors with field zero or strengthen the callback domain.
theorem short_vector {α : Type} (xs : List α) (r : Nat) (hr : r < 1024) (hshort : xs.length ≤ r) :
    (probe xs).val[r]'(by have h := (probe xs).property; scalar_tac) = none := by
  rw [probe_value]
  exact List.getElem?_eq_none hshort

#print axioms probe_value
#print axioms column_value
#print axioms short_vector
end PV_B3P_HelperView224
