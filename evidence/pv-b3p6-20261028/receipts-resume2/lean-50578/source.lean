import PV_B3P_Chunk64Success226V3
namespace PV_B3P_EncodeSuccess226V3
open Aeneas Aeneas.Std PV_B3P_226V3
set_option autoImplicit false
set_option maxRecDepth 2048

theorem success (p : reference226.OwnedPublic)
    (h : ∀ j : Usize, ∃ v, reference226.byte_at p j = .ok (.Ok v)) :
    ∃ out, reference226.encode_owned p = .ok (.Ok out) := by
  obtain ⟨c0,h0⟩ := PV_B3P_Chunk64Success226V3.success p 0#usize h
  obtain ⟨c1,h1⟩ := PV_B3P_Chunk64Success226V3.success p 64#usize h
  obtain ⟨c2,h2⟩ := PV_B3P_Chunk64Success226V3.success p 128#usize h
  obtain ⟨c3,h3⟩ := PV_B3P_Chunk64Success226V3.success p 192#usize h
  obtain ⟨c4,h4⟩ := PV_B3P_Chunk64Success226V3.success p 256#usize h
  obtain ⟨c5,h5⟩ := PV_B3P_Chunk64Success226V3.success p 320#usize h
  obtain ⟨c6,h6⟩ := PV_B3P_Chunk64Success226V3.success p 384#usize h
  obtain ⟨c7,h7⟩ := PV_B3P_Chunk64Success226V3.success p 448#usize h
  obtain ⟨c8,h8⟩ := PV_B3P_Chunk64Success226V3.success p 512#usize h
  obtain ⟨c9,h9⟩ := PV_B3P_Chunk64Success226V3.success p 576#usize h
  obtain ⟨c10,h10⟩ := PV_B3P_Chunk64Success226V3.success p 640#usize h
  obtain ⟨c11,h11⟩ := PV_B3P_Chunk64Success226V3.success p 704#usize h
  obtain ⟨c12,h12⟩ := PV_B3P_Chunk64Success226V3.success p 768#usize h
  obtain ⟨c13,h13⟩ := PV_B3P_Chunk64Success226V3.success p 832#usize h
  obtain ⟨c14,h14⟩ := PV_B3P_Chunk64Success226V3.success p 896#usize h
  obtain ⟨c15,h15⟩ := PV_B3P_Chunk64Success226V3.success p 960#usize h
  obtain ⟨c16,h16⟩ := PV_B3P_Chunk64Success226V3.success p 1024#usize h
  obtain ⟨c17,h17⟩ := PV_B3P_Chunk64Success226V3.success p 1088#usize h
  obtain ⟨c18,h18⟩ := PV_B3P_Chunk64Success226V3.success p 1152#usize h
  obtain ⟨c19,h19⟩ := PV_B3P_Chunk64Success226V3.success p 1216#usize h
  obtain ⟨c20,h20⟩ := PV_B3P_Chunk64Success226V3.success p 1280#usize h
  obtain ⟨c21,h21⟩ := PV_B3P_Chunk64Success226V3.success p 1344#usize h
  obtain ⟨c22,h22⟩ := PV_B3P_Chunk64Success226V3.success p 1408#usize h
  unfold reference226.encode_owned
  cases hp : p.withdrawal with
  | false =>
    have hu : { p with withdrawal := false } = p := by cases p; simp_all
    simp only [hp,Bool.false_eq_true,↓reduceIte,bind_tc_ok,hu,
      h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,
      core.result.Result.Insts.CoreOpsTry.branch]
    exact ⟨_,rfl⟩
  | true =>
    have hu : { p with withdrawal := true } = p := by cases p; simp_all
    simp only [hp,Bool.false_eq_true,↓reduceIte,bind_tc_ok,hu,
      h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,
      core.result.Result.Insts.CoreOpsTry.branch]
    exact ⟨_,rfl⟩

#print axioms success
end PV_B3P_EncodeSuccess226V3
