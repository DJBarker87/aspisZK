import Stage2ReaderSuccess

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1Stage2AdoptedReader.ResumeFixedPrefix

open AspisR1Stage2AdoptedReader

private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (v : B)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- The fixed, allocation-free read prefix immediately after c8's resume
    authentication checks. It is the source-order cut through the successful
    `rho = r.k()?` read; query-array and later mutable loops are excluded. -/
def readPrefix (d : ReaderDecoders) (bytes : Slice Std.U8) :
    Result ((Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 32#usize ×
      core.result.Result aspis_core.field.WideExact verifier.Error ×
      core.result.Result aspis_core.field.WideExact verifier.Error ×
      core.result.Result aspis_core.field.WideExact verifier.Error ×
      core.result.Result aspis_core.field.WideExact verifier.Error ×
      core.result.Result aspis_core.field.QM31 verifier.Error) × verifier.Reader) := do
  let r0 : verifier.Reader := { bytes := bytes, «at» := 80#usize }
  let (state, r1) ← verifier.Reader.raw d 32#usize r0
  let (root0, r2) ← verifier.Reader.raw d 32#usize r1
  let (root1, r3) ← verifier.Reader.raw d 32#usize r2
  let (gamma, r4) ← verifier.Reader.e d r3
  let (kappa, r5) ← verifier.Reader.e d r4
  let (alpha0, r6) ← verifier.Reader.e d r5
  let (alpha1, r7) ← verifier.Reader.e d r6
  let (rho, r8) ← verifier.Reader.k d r7
  ok ((state, root0, root1, gamma, kappa, alpha0, alpha1, rho), r8)

/-- A successful execution of the source-ordered fixed prefix necessarily
    reached every strict field decoder and decoded rho from the final 16-byte
    read. Cursor provenance remains expressed as the individual checked reads,
    avoiding any unchecked natural-number cursor arithmetic. -/
theorem successful_prefix_decodes
    (d : ReaderDecoders) (bytes : Slice Std.U8)
    (state root0 root1 : Array Std.U8 32#usize)
    (gamma kappa alpha0 alpha1 : aspis_core.field.WideExact)
    (rho : aspis_core.field.QM31)
    (rfinal : verifier.Reader)
    (h : readPrefix d bytes = ok
      ((state, root0, root1, .Ok gamma, .Ok kappa, .Ok alpha0, .Ok alpha1, .Ok rho), rfinal)) :
    ∃ r1 r2 r3 r4 r5 r6 r7,
      verifier.Reader.raw d 32#usize { bytes := bytes, «at» := 80#usize } = ok (state, r1) ∧
      verifier.Reader.raw d 32#usize r1 = ok (root0, r2) ∧
      verifier.Reader.raw d 32#usize r2 = ok (root1, r3) ∧
      verifier.Reader.e d r3 = ok (.Ok gamma, r4) ∧
      verifier.Reader.e d r4 = ok (.Ok kappa, r5) ∧
      verifier.Reader.e d r5 = ok (.Ok alpha0, r6) ∧
      verifier.Reader.e d r6 = ok (.Ok alpha1, r7) ∧
      verifier.Reader.k d r7 = ok (.Ok rho, rfinal) ∧
      (∃ rawGamma : Array Std.U8 32#usize,
        verifier.Reader.raw d 32#usize r3 = ok (rawGamma, r4) ∧
        d.wide rawGamma.to_slice = ok (some gamma)) ∧
      (∃ rawKappa : Array Std.U8 32#usize,
        verifier.Reader.raw d 32#usize r4 = ok (rawKappa, r5) ∧
        d.wide rawKappa.to_slice = ok (some kappa)) ∧
      (∃ rawAlpha0 : Array Std.U8 32#usize,
        verifier.Reader.raw d 32#usize r5 = ok (rawAlpha0, r6) ∧
        d.wide rawAlpha0.to_slice = ok (some alpha0)) ∧
      (∃ rawAlpha1 : Array Std.U8 32#usize,
        verifier.Reader.raw d 32#usize r6 = ok (rawAlpha1, r7) ∧
        d.wide rawAlpha1.to_slice = ok (some alpha1)) ∧
      (∃ rawRho : Array Std.U8 16#usize,
        verifier.Reader.raw d 16#usize r7 = ok (rawRho, rfinal) ∧
        d.qm rawRho.to_slice = ok (some rho)) := by
  unfold readPrefix at h
  obtain ⟨p0, hp0, h⟩ := bind_success _ _ _ h
  obtain ⟨state', r1⟩ := p0
  obtain ⟨p1, hp1, h⟩ := bind_success _ _ _ h
  obtain ⟨root0', r2⟩ := p1
  obtain ⟨p2, hp2, h⟩ := bind_success _ _ _ h
  obtain ⟨root1', r3⟩ := p2
  obtain ⟨p3, hp3, h⟩ := bind_success _ _ _ h
  obtain ⟨gamma', r4⟩ := p3
  obtain ⟨p4, hp4, h⟩ := bind_success _ _ _ h
  obtain ⟨kappa', r5⟩ := p4
  obtain ⟨p5, hp5, h⟩ := bind_success _ _ _ h
  obtain ⟨alpha0', r6⟩ := p5
  obtain ⟨p6, hp6, h⟩ := bind_success _ _ _ h
  obtain ⟨alpha1', r7⟩ := p6
  obtain ⟨p7, hp7, h⟩ := bind_success _ _ _ h
  obtain ⟨rho', r8⟩ := p7
  cases h
  have hgamma := ReaderSuccess.wide_success d r3 r4 gamma hp3
  have hkappa := ReaderSuccess.wide_success d r4 r5 kappa hp4
  have halpha0 := ReaderSuccess.wide_success d r5 r6 alpha0 hp5
  have halpha1 := ReaderSuccess.wide_success d r6 r7 alpha1 hp6
  have hrho := ReaderSuccess.qm_success d r7 rfinal rho hp7
  rcases hgamma with ⟨rawGamma,hrawGamma,hdecGamma,_,_⟩
  rcases hkappa with ⟨rawKappa,hrawKappa,hdecKappa,_,_⟩
  rcases halpha0 with ⟨rawAlpha0,hrawAlpha0,hdecAlpha0,_,_⟩
  rcases halpha1 with ⟨rawAlpha1,hrawAlpha1,hdecAlpha1,_,_⟩
  rcases hrho with ⟨rawRho, hrawRho, hdecodeRho, _, _⟩
  exact ⟨r1,r2,r3,r4,r5,r6,r7,hp0,hp1,hp2,hp3,hp4,hp5,hp6,hp7,
    ⟨rawGamma,hrawGamma,hdecGamma⟩,
    ⟨rawKappa,hrawKappa,hdecKappa⟩,
    ⟨rawAlpha0,hrawAlpha0,hdecAlpha0⟩,
    ⟨rawAlpha1,hrawAlpha1,hdecAlpha1⟩,
    ⟨rawRho,hrawRho,hdecodeRho⟩⟩

#print axioms successful_prefix_decodes

end AspisR1Stage2AdoptedReader.ResumeFixedPrefix
