
abbrev fle0 := PCVU_QM31.PCVU_Fresh.field.QM31.from_le_bytes

theorem frk {B : Type} (r : verifier.Reader)
    (K : core.result.Result aspis_core.field.QM31 VErr × verifier.Reader → Result B) :
    (PCVU_Fresh2.verifier.Reader.k fle0 r >>= K) =
      (CheckpointBytes3Reader.readK r >>= fun p => K (phi p.1, p.2)) := by
  unfold PCVU_Fresh2.verifier.Reader.k CheckpointBytes3Reader.readK
  have hraw : PCVU_Fresh2.verifier.Reader.raw 16#usize r = CheckpointBytes3Reader.raw 16#usize r := rfl
  rw [hraw]
  simp only [bind_assoc, bind_tc_ok, lift]
  congr 1; funext p
  rcases p with ⟨b, out⟩
  have w : b.to_slice.val.length = 16 := by simpa [Array.to_slice] using b.property
  rw [PCVU_QM31.qm31_16 b.to_slice w]
  simp only [bind_assoc, bind_tc_ok]
  congr 1; funext q
  cases q <;> rfl

#print axioms frk
