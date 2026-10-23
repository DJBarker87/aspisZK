import S2C_GuardDrop
set_option autoImplicit false
namespace AspisR1.S2C
open S2Trust

theorem copy_lookup {F : Type} (s : Heap F) (g : Guard)
    (source : Nat → UInt8) (n t : Nat) :
    lookup (copyPrefix s g source n) t = lookup s t := by
  unfold lookup
  rw [(copy_structural_frame s g source n).2.2.2.2.2.1]

theorem copy_valid {F : Type} (s : Heap F) (g : Guard)
    (source : Nat → UInt8) (n : Nat) (valid : Valid s) :
    Valid (copyPrefix s g source n) := by
  obtain ⟨accounts,live,allocated,counter,external,guards,ambient⟩ :=
    copy_structural_frame s g source n
  rcases valid with ⟨linear,counters,descriptors,owners⟩
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [guards] using linear
  · simpa only [counter,external,count,guards] using counters
  · intro h mem
    rw [guards] at mem
    obtain ⟨ha,hd⟩ := descriptors h mem
    exact ⟨allocated ▸ ha, hd.trans (copy_descriptor s g source n h.cell).symm⟩
  · simpa only [live,accounts,allocated] using owners

/-- Primitive simulation is iterated along the FIXED native cuts of e. Initial
relatedness, source snapshot and all actual write steps refer to that same e.
This is not a proof that :985 lowers to these steps: the native copy/source
interpretation remains a concrete caller obligation. -/
theorem native_copy_cuts {E W F : Type} (L : Library W F)
    (trust : S2TrustedSdkBorrow L) (native : E → Nat → W)
    (initial : E → Heap F) (source : E → Nat → UInt8)
    (e : E) (g : Guard) (width : Nat)
    (related : L.related (native e 0) (initial e))
    (valid : Valid (initial e)) (found : lookup (initial e) g.token = some g)
    (kind : g.kind = .exclusive)
    (length : ((initial e).payload g.cell).descriptor.length = width)
    (actual : ∀ i, i < width →
      L.run (native e i) (.write g.token i (source e i)) = (native e (i+1), .unit)) :
    ∀ n, n ≤ width → L.related (native e n) (copyPrefix (initial e) g (source e) n) := by
  intro n bound
  induction n with
  | zero => exact related
  | succ n ih =>
    have lt : n < width := by omega
    have rn := ih (Nat.le_of_lt lt)
    have vn := copy_valid (initial e) g (source e) n valid
    have gn : lookup (copyPrefix (initial e) g (source e) n) g.token = some g := by
      rw [copy_lookup]; exact found
    have len : n < ((copyPrefix (initial e) g (source e) n).payload g.cell).descriptor.length := by
      rw [copy_descriptor,length]; exact lt
    exact fixed_cut L _ _ _ _ _ (actual n lt)
      ((trust.exclusive_deref _ _ _ _ rn vn gn kind).2 n (source e n) len)

/-- Final native payload observations come from the copied state of e. Proof
and public payload identities include original descriptors and all byte positions.
The original-to-copy-cut readonly frame is deliberately explicit. -/
theorem native_copy_output {E W F : Type} (L : Library W F)
    (trust : S2TrustedSdkBorrow L) (native : E → Nat → W)
    (initial : E → Heap F) (source : E → Nat → UInt8)
    (e : E) (g : Guard) (proof pubCell : Nat)
    (related : L.related (native e 0) (initial e)) (valid : Valid (initial e))
    (found : lookup (initial e) g.token = some g) (kind : g.kind = .exclusive)
    (length : ((initial e).payload g.cell).descriptor.length = 1768)
    (separateProof : proof ≠ g.cell) (separatePublic : pubCell ≠ g.cell)
    (actual : ∀ i, i < 1768 →
      L.run (native e i) (.write g.token i (source e i)) = (native e (i+1), .unit)) :
    (∀ i, i < 1768 → (L.cellPayload (native e 1768) g.cell).contents i = source e i) ∧
    L.cellPayload (native e 1768) proof = (initial e).payload proof ∧
    L.cellPayload (native e 1768) pubCell = (initial e).payload pubCell := by
  have relatedEnd := native_copy_cuts L trust native initial source e g 1768
    related valid found kind length actual 1768 (Nat.le_refl _)
  have validEnd := copy_valid (initial e) g (source e) 1768 valid
  have payload := trust.cell_payload _ _ relatedEnd validEnd
  obtain ⟨cp,pf,pub,_⟩ := checkpoint_copy_regions (initial e) g (source e)
    proof pubCell separateProof separatePublic
  exact ⟨fun i hi => congrArg (fun p : Payload => p.contents i) (payload g.cell) |>.trans (cp i hi),
    (payload proof).trans pf, (payload pubCell).trans pub⟩

#print axioms copy_lookup
#print axioms copy_valid
#print axioms native_copy_cuts
#print axioms native_copy_output
end AspisR1.S2C
