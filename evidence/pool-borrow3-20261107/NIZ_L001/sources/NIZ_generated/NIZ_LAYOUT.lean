import NIO_Cpi
import AdapterRwRuntimeAdmission
set_option autoImplicit false
namespace NIZ_LAYOUT

inductive DepositMode where
  | fresh | same | rollover
  deriving DecidableEq

def depositStart : DepositMode → Nat
  | .fresh | .same => 3
  | .rollover => 4

def DepositGuard (m : DepositMode) (g : Nat) : Prop :=
  g = 1 ∨ (m = .rollover ∧ g = 3) ∨ (m ≠ .rollover ∧ g = 2)

/-- pair_forest.rs:1033..1082, 1093..1196. All three source modes. -/
theorem deposit_separate (m : DepositMode) (g o : Nat)
    (hg : DepositGuard m g) : g ≠ depositStart m + o := by
  cases m <;> simp only [DepositGuard, depositStart] at * <;>
    rcases hg with hg | ⟨hm,hg⟩ | ⟨hm,hg⟩ <;> simp_all <;> omega
#print axioms deposit_separate

/-- pair_forest.rs:1292..1307. Includes genesis, same-page and rollover. -/
theorem terminal_separate (cursor g o : Nat)
    (hc : cursor = 4 ∨ cursor = 5)
    (hg : g = 2 ∨ g = 3 ∨ (cursor = 5 ∧ g = 4) ∨ g = cursor) :
    g ≠ cursor + 7 + o := by
  rcases hc with hc | hc <;> rcases hg with hg | hg | ⟨hc2,hg⟩ | hg <;> omega
#print axioms terminal_separate

/-- pair_processor.rs:126..164, proof_index + 1 is marker_index + 5. -/
theorem pair_separate (marker g o : Nat) (hg : g ≤ marker) :
    g ≠ (marker + 4) + 1 + o := by omega
#print axioms pair_separate

/-- Processor withdrawal callback: held pool/current/next precede marker;
marker, payer, system and all five token positions start at marker. -/
theorem withdrawal_callback_separate (marker g t : Nat)
    (hg : g < marker) (ht : marker ≤ t) : g ≠ t := by omega
#print axioms withdrawal_callback_separate

/-- Deposits reject every equal-key state/token pair before entering transition. -/
theorem deposit_callback_key_separate {Key : Type} (keys : Nat → Key)
    (state token : Nat → Prop)
    (checked : ∀ g t, state g → token t → keys g ≠ keys t)
    (g t : Nat) (hg : state g) (ht : token t) : keys g ≠ keys t :=
  checked g t hg ht
#print axioms deposit_callback_key_separate

/-- Ruling (ap), applied to the exact seven-field entry admission, not a new axiom.
This concerns the entry account-cell map; native preservation to each cut remains
an explicit source obligation. -/
theorem entry_cells_separate {F : Type} (s : AspisR1.S2Trust.Heap F)
    (keys : Nat → List UInt8) (n g t : Nat)
    (admission : AspisR1.AdapterRw.RuntimeEntrypointAdmission s keys n)
    (unique : ∀ i j, i < n → j < n → i ≠ j → keys i ≠ keys j)
    (hg : g < n) (ht : t < n) (separate : g ≠ t) :
    (s.accounts g).1 ≠ (s.accounts t).1 :=
  AspisR1.AdapterRw.distinct_keys_distinct_cells admission hg ht
    (unique g t hg ht separate)
#print axioms entry_cells_separate

/-- Whole passed-footprint exclusion follows pointwise, with actual bounds.
No frame law, runtime success or callback footprint is hidden in the conclusion. -/
theorem entry_footprints_disjoint {F : Type} (s : AspisR1.S2Trust.Heap F)
    (keys : Nat → List UInt8) (n : Nat) (guard passed : Nat → Prop)
    (admission : AspisR1.AdapterRw.RuntimeEntrypointAdmission s keys n)
    (unique : ∀ i j, i < n → j < n → i ≠ j → keys i ≠ keys j)
    (guardBound : ∀ g, guard g → g < n)
    (passedBound : ∀ t, passed t → t < n)
    (indices : ∀ g t, guard g → passed t → g ≠ t) :
    ∀ g t, guard g → passed t → (s.accounts g).1 ≠ (s.accounts t).1 := by
  intro g t hg ht
  exact entry_cells_separate s keys n g t admission unique
    (guardBound g hg) (passedBound t ht) (indices g t hg ht)
#print axioms entry_footprints_disjoint
end NIZ_LAYOUT
