import PaymentMaskRead
import SelectedTransferPositive

/-! Deterministic layout contract for the research adapter that retains the
legacy random-mask draws/balancer, then overwrites ACTIVE row1014/column3 with
the inverse witness before C1 commitment. No uniformity, simulator, Rust
translation, acceptance, or efficient-extraction theorem is asserted here.
-/
set_option autoImplicit false
namespace AspisV8.SelectedTransferMaskAdapter
open AspisV8.PaymentMaskRead
open AspisFormal.ArithmetizationCore

def reserved (r c : Nat) : Prop := r=1014 ∧ c=3
def remainingMask (r c : Nat) : Prop := maskCell r c ∧ ¬reserved r c

theorem reserved_was_mask : maskCell 1014 3 := by
  have notValue : ¬valueUsed 1014 3 := by
    rintro (⟨v,hv,hr,_⟩ | ⟨_,hc⟩ | ⟨hr,_⟩)
    · interval_cases v <;> norm_num at hr <;> revert hr <;> decide
    · omega
    · omega
  refine Or.inr ⟨by omega, ?_⟩
  rintro (⟨hr,_⟩ | ⟨_,hv|ho⟩)
  · omega
  · exact notValue hv
  · rcases ho with ⟨hr,_⟩ | ⟨hr,_⟩ <;> omega

theorem protected_not_reserved (r c : Nat) (h : ¬maskCell r c) :
    ¬reserved r c := by
  rintro ⟨rfl,rfl⟩
  exact h reserved_was_mask

theorem decoder_not_reserved (r c : Nat) (h : readCell r c) :
    ¬reserved r c := protected_not_reserved r c (read_not_mask r c h)

theorem remaining_mask_preserves_decoder (r c : Nat) (h : readCell r c) :
    ¬remainingMask r c := fun hm => read_not_mask r c h hm.1

noncomputable def overwrite {K : Type*} (t : Nat → Nat → K) (u : K)
    (r c : Nat) : K := by
  classical
  exact if reserved r c then u else t r c

theorem overwrite_reserved {K : Type*} (t : Nat → Nat → K) (u : K) :
    overwrite t u 1014 3=u := by simp [overwrite,reserved]

theorem overwrite_else {K : Type*} (t : Nat → Nat → K) (u : K)
    (r c : Nat) (h : ¬reserved r c) : overwrite t u r c=t r c := by
  simp only [overwrite,if_neg h]

noncomputable def inactiveRows (rows : Finset Nat) (active : Nat → Prop) : Finset Nat := by
  classical
  exact rows.filter (fun r => ¬active r)

/-- Field-level shape of balance_m31_copy_inactive, applied independently to
each of the 16 semantic columns. The source's range/filter has distinct rows,
so its omitted-dependent sum is exactly this finite erase sum. -/
noncomputable def balance {K : Type*} [AddCommGroup K] (rows : Finset Nat)
    (active : Nat → Prop) (dep : Nat → Nat) (t : Nat → Nat → K) (r c : Nat) : K := by
  classical
  exact if c<16 ∧ r=dep c then
    -(∑ s ∈ (inactiveRows rows active).erase (dep c), t s c) else t r c

/-- Actual source selection chooses a dependent from the allowed-mask list,
not an arbitrary inactive semantic cell. Inactivity is a separate premise. -/
def DependentMaskSupport (dep : Nat → Nat) : Prop :=
  ∀ c, c<16 → maskCell (dep c) c

theorem balance_protected {K : Type*} [AddCommGroup K] (rows : Finset Nat)
    (active : Nat → Prop) (dep : Nat → Nat) (t : Nat → Nat → K)
    (support : DependentMaskSupport dep) (r c : Nat) (h : ¬maskCell r c) :
    balance rows active dep t r c=t r c := by
  have hn : ¬(c<16 ∧ r=dep c) := by
    rintro ⟨hc,hr⟩
    apply h
    rw [hr]
    exact support c hc
  simp only [balance,if_neg hn]

theorem balanced_inactive_sum_zero {K : Type*} [AddCommGroup K]
    (rows : Finset Nat) (active : Nat → Prop) (dep : Nat → Nat)
    (t : Nat → Nat → K) (c : Nat) (hc : c<16)
    (hmem : dep c ∈ rows) (hinactive : ¬active (dep c)) :
    (∑ r ∈ inactiveRows rows active, balance rows active dep t r c)=0 := by
  classical
  let I := inactiveRows rows active
  have hd : dep c ∈ I := Finset.mem_filter.mpr ⟨hmem,hinactive⟩
  have rest : (∑ r ∈ I.erase (dep c), balance rows active dep t r c)=
      ∑ r ∈ I.erase (dep c),t r c := by
    apply Finset.sum_congr rfl
    intro r hr
    have hn := (Finset.mem_erase.mp hr).1
    have hg : ¬(c<16 ∧ r=dep c) := fun h => hn h.2
    exact if_neg hg
  have finish : balance rows active dep t (dep c) c=
      -(∑ r ∈ I.erase (dep c),t r c) := if_pos ⟨hc,rfl⟩
  calc
    (∑ r ∈ I, balance rows active dep t r c) =
        (∑ r ∈ I.erase (dep c), balance rows active dep t r c)+
          balance rows active dep t (dep c) c :=
      (Finset.sum_erase_add _ _ hd).symm
    _ = (∑ r ∈ I.erase (dep c),t r c) -
        (∑ r ∈ I.erase (dep c),t r c) := by
      rw [rest,finish]
      rw [sub_eq_add_neg]
    _ = 0 := sub_self _

/-- Restoring the inverse AFTER balancing does not disturb any inactive
column sum: its row is already Copy-active, independent of its column. -/
theorem overwrite_preserves_inactive_sum {K : Type*} [AddCommMonoid K]
    (rows : Finset Nat) (active : Nat → Prop) (t : Nat → Nat → K)
    (u : K) (c : Nat) (ha : active 1014) :
    (∑ r ∈ inactiveRows rows active,overwrite t u r c)=
      ∑ r ∈ inactiveRows rows active,t r c := by
  classical
  apply Finset.sum_congr rfl
  intro r hr
  have hi := (Finset.mem_filter.mp hr).2
  have hn : ¬reserved r c := by
    rintro ⟨rfl,_⟩
    exact hi ha
  exact overwrite_else t u r c hn

noncomputable def adapter {K : Type*} [AddCommGroup K] (rows : Finset Nat)
    (active : Nat → Prop) (dep : Nat → Nat) (t delta : Nat → Nat → K)
    (u : K) : Nat → Nat → K :=
  overwrite (balance rows active dep (applyMasks t delta)) u

theorem adapter_protected {K : Type*} [AddCommGroup K] (rows : Finset Nat)
    (active : Nat → Prop) (dep : Nat → Nat) (t delta : Nat → Nat → K)
    (u : K) (support : DependentMaskSupport dep)
    (r c : Nat) (h : ¬maskCell r c) :
    adapter rows active dep t delta u r c=t r c := by
  rw [adapter,overwrite_else _ _ _ _ (protected_not_reserved r c h),
    balance_protected _ _ _ _ support _ _ h]
  exact if_neg h

/-- All decoder reads survive arbitrary legacy masks, source-supported
balancing overwrites, and the final reserved-cell restoration. -/
theorem adapter_decoder_reads {K : Type*} [AddCommGroup K] (rows : Finset Nat)
    (active : Nat → Prop) (dep : Nat → Nat) (t delta : Nat → Nat → K)
    (u : K) (support : DependentMaskSupport dep)
    (r c : Nat) (h : readCell r c) :
    adapter rows active dep t delta u r c=t r c :=
  adapter_protected rows active dep t delta u support r c (read_not_mask r c h)

theorem adapter_inactive_sum_zero {K : Type*} [AddCommGroup K]
    (rows : Finset Nat) (active : Nat → Prop) (dep : Nat → Nat)
    (t delta : Nat → Nat → K) (u : K) (c : Nat) (hc : c<16)
    (hmem : dep c ∈ rows) (hinactive : ¬active (dep c)) (ha : active 1014) :
    (∑ r ∈ inactiveRows rows active,adapter rows active dep t delta u r c)=0 := by
  rw [adapter,overwrite_preserves_inactive_sum _ _ _ _ _ ha]
  exact balanced_inactive_sum_zero rows active dep _ c hc hmem hinactive

theorem value_used_not_mask (r c : Nat) (hr : 1008≤r) (h : valueUsed r c) :
    ¬maskCell r c := by
  rintro (⟨hlo,_⟩ | ⟨_,hn⟩)
  · omega
  · exact hn (Or.inr ⟨hr,Or.inl h⟩)

theorem recipient_local_protected : ¬maskCell 1014 1 :=
  value_used_not_mask 1014 1 (by omega) (Or.inr (Or.inl ⟨rfl,by omega⟩))

theorem change_local_protected : ¬maskCell 1015 1 :=
  value_used_not_mask 1015 1 (by omega) (Or.inr (Or.inr ⟨rfl,by omega⟩))

/-- The adapter's actual three-cell product residual reduces to the original
amount factors and supplied inverse, despite legacy draw/balance work. -/
theorem adapter_product_residual (rows : Finset Nat) (active : Nat → Prop)
    (dep : Nat → Nat) (t delta : Nat → Nat → F) (u : F)
    (support : DependentMaskSupport dep) :
    SelectedTransferPositive.ProductInverseResidual (adapter rows active dep t delta u) ↔
      t 1014 1*t 1015 1*u-1=0 := by
  unfold SelectedTransferPositive.ProductInverseResidual
  rw [adapter_protected _ _ _ _ _ _ support _ _ recipient_local_protected,
    adapter_protected _ _ _ _ _ _ support _ _ change_local_protected]
  simp only [adapter,overwrite_reserved]

theorem original_mask_writes_reserved {K : Type*} [Add K]
    (t delta : Nat → Nat → K) : applyMasks t delta 1014 3=t 1014 3+delta 1014 3 :=
  if_pos reserved_was_mask

#print axioms reserved_was_mask
#print axioms remaining_mask_preserves_decoder
#print axioms balanced_inactive_sum_zero
#print axioms overwrite_preserves_inactive_sum
#print axioms adapter_protected
#print axioms adapter_decoder_reads
#print axioms adapter_inactive_sum_zero
#print axioms adapter_product_residual
#print axioms original_mask_writes_reserved
end AspisV8.SelectedTransferMaskAdapter
