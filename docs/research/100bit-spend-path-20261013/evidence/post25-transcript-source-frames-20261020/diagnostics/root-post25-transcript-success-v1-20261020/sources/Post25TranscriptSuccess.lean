import Post25TranscriptExplicitSamplers
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1Post25Transcript.TranscriptSuccess
abbrev Bytes32 := Array U8 32#usize

def absorbParts (state : Bytes32) (tag : U8) (payload : Slice U8) : Slice (Slice U8) :=
  Array.to_slice (Array.make 4#usize [Array.to_slice state,
    Array.to_slice (Array.make 2#usize [0#u8,tag]),
    Array.to_slice (core.num.U32.to_le_bytes (UScalar.cast .U32 (Slice.len payload))),payload])

def readParts (state : Bytes32) (tag : U8) : Slice (Slice U8) :=
  Array.to_slice (Array.make 2#usize [Array.to_slice state,
    Array.to_slice (Array.make 1#usize [tag])])

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β)
    (v : β) (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem absorb_eq {H : Type} (D : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (row tag : U8) (payload : Slice U8)
    (htag : 160#u8 + row = .ok tag) :
    transcript.Transcript.absorb D self row payload =
      (do let absorbed ← D.digest self.hash (absorbParts self.state tag payload)
          .ok { self with state := absorbed }) := by
  simp only [transcript.Transcript.absorb,lift,bind_tc_ok,htag,absorbParts]

theorem block_eq {H : Type} (D : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (row tag : U8) (payload : Slice U8)
    (htag : 160#u8 + row = .ok tag) :
    transcript.Transcript.block D self row payload =
      (do let absorbed ← D.digest self.hash (absorbParts self.state tag payload)
          let block ← D.digest self.hash (readParts absorbed 1#u8)
          let state ← D.digest self.hash (readParts absorbed 2#u8)
          .ok (block,{self with state := state})) := by
  simp only [transcript.Transcript.block,absorb_eq D self row tag payload htag,
    bind_assoc_eq,lift,bind_tc_ok,readParts]

theorem block_success {H : Type} (D : aspis_core.Digest32 H)
    (self after : transcript.Transcript H) (row tag : U8) (payload : Slice U8)
    (block : Bytes32) (htag : 160#u8 + row = .ok tag)
    (h : transcript.Transcript.block D self row payload = .ok (block,after)) :
    ∃ absorbed state,
      D.digest self.hash (absorbParts self.state tag payload) = .ok absorbed ∧
      D.digest self.hash (readParts absorbed 1#u8) = .ok block ∧
      D.digest self.hash (readParts absorbed 2#u8) = .ok state ∧
      after = {self with state := state} := by
  rw [block_eq D self row tag payload htag] at h
  obtain ⟨absorbed,habs,h⟩ := bind_success _ _ _ h
  obtain ⟨block1,hread,h⟩ := bind_success _ _ _ h
  obtain ⟨state,hstate,h⟩ := bind_success _ _ _ h
  have he := Result.ok.inj h
  have hb := congrArg Prod.fst he
  have ha := congrArg Prod.snd he
  change block1 = block at hb
  change {self with state := state} = after at ha
  subst block1
  exact ⟨absorbed,state,habs,hread,hstate,ha.symm⟩

theorem scalar_success (ops : SamplerOps) {H : Type} (D : aspis_core.Digest32 H)
    (self after : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (nonzero : Bool) (value : aspis_core.field.WideExact)
    (h : transcript.Transcript.scalar ops D self row payload nonzero = .ok (value,after)) :
    ∃ block,
      transcript.Transcript.block D self row payload = .ok (block,after) ∧
      (if nonzero then ops.gamma block else ops.ordinary block) = .ok value := by
  unfold transcript.Transcript.scalar at h
  obtain ⟨pair,hblock,h⟩ := bind_success _ _ _ h
  rcases pair with ⟨block,after1⟩
  obtain ⟨value1,hsample,h⟩ := bind_success _ _ _ h
  simp only [lift,bind_tc_ok,trace.value] at h
  have he := Result.ok.inj h
  have hv := congrArg Prod.fst he
  have ha := congrArg Prod.snd he
  change value1 = value at hv
  change after1 = after at ha
  subst value1; subst after1
  exact ⟨block,hblock,hsample⟩

theorem scalar_k_success (ops : SamplerOps) {H : Type} (D : aspis_core.Digest32 H)
    (self after : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (value : aspis_core.field.QM31)
    (h : transcript.Transcript.scalar_k ops D self row payload = .ok (value,after)) :
    ∃ block embedded,
      transcript.Transcript.block D self row payload = .ok (block,after) ∧
      ops.qm31 block = .ok value ∧ ops.embed value = .ok embedded := by
  unfold transcript.Transcript.scalar_k at h
  obtain ⟨pair,hblock,h⟩ := bind_success _ _ _ h
  rcases pair with ⟨block,after1⟩
  obtain ⟨value1,hsample,h⟩ := bind_success _ _ _ h
  simp only [lift,bind_tc_ok] at h
  obtain ⟨embedded,hembed,h⟩ := bind_success _ _ _ h
  simp only [trace.value,bind_tc_ok] at h
  have he := Result.ok.inj h
  have hv := congrArg Prod.fst he
  have ha := congrArg Prod.snd he
  change value1 = value at hv
  change after1 = after at ha
  subst value1; subst after1
  exact ⟨block,embedded,hblock,hsample,hembed⟩
#print axioms absorb_eq
#print axioms block_eq
#print axioms block_success
#print axioms scalar_success
#print axioms scalar_k_success
end AspisR1Post25Transcript.TranscriptSuccess
