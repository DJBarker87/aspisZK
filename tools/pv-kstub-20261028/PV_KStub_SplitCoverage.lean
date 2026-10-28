import PV_KStub_WindowFrame
namespace PV_KStub_SplitCoverage
/-- Both runtime windows must cover the entire property, including length metadata. -/
theorem metadata_and_bytes (L B : Nat → Prop)
    (lo : ∀ n, n≤129 → n≤64 → L n ∧ B n)
    (hi : ∀ n, n≤129 → 64<n → L n ∧ B n) :
    ∀ n, n≤129 → L n ∧ B n :=
  PV_KStub_WindowFrame.split_windows (fun n => L n ∧ B n) lo hi
/-- No claim follows about the unconfirmed high window from a low-window proof. -/
theorem high_nonempty : 64<129 ∧ 129≤129 := ⟨by decide, Nat.le_refl _⟩
#print axioms metadata_and_bytes
#print axioms high_nonempty
end PV_KStub_SplitCoverage
