import R1Z.CertData

/-! D49.4 C3: `DataOK` gives the BCondG Props (`EchOK` on the supplied column
list, `PreOK₂` for the V_G preimages of the `n_f`) and the lift Props (`RinvOK`),
over any field `F` receiving `ZP` by a ring hom `φ`. -/

set_option autoImplicit false

namespace R1Z.CertData

open scoped BigOperators
open R1Z.CertSound

section Field

variable {F : Type*} [Field F] (φ : ZP →+* F)

theorem phi_ite (p : Prop) [Decidable p] : φ (if p then 1 else 0) = if p then 1 else 0 := by
  by_cases h : p <;> simp [h]

/-- The pivot columns `lst[0..r)`. -/
def pivF (d : CData) {B : ℕ} (hd : DataOK d) (hB : d.bw = B) (a : Fin d.r) : Fin B :=
  ⟨d.lst a, by
    obtain ⟨-, -, -, -, ⟨hl1, hl2, hrk, -, hpl, -⟩⟩ := hd
    have := (hpl a (by omega)).1
    omega⟩

/-- The free columns `lst[r..r+k)`. -/
def frF (d : CData) {B : ℕ} (hd : DataOK d) (hB : d.bw = B) (f : Fin d.k) : Fin B :=
  ⟨d.lst (d.r + f), by
    obtain ⟨-, -, -, -, ⟨hl1, hl2, hrk, -, hpl, -⟩⟩ := hd
    have := (hpl (d.r + f) (by omega)).1
    omega⟩

theorem emat_eq (d : CData) (hd : DataOK d) {B : ℕ} (hB : d.bw = B) (a : Fin d.r) (c : Fin B) :
    Emat (fun (a : Fin d.r) (x : Fin d.q) => φ (rowM d.u d.q a x))
      (fun (x : Fin d.q) (c : Fin B) => φ (rowM d.rel d.bw x c)) a c = φ (rowM d.e d.bw a c) := by
  obtain ⟨-, -, -, -, ⟨-, -, -, hUR, -⟩⟩ := hd
  have := hUR a a.2 c (hB ▸ c.2)
  simp only [zero_add] at this
  unfold Emat rowM
  rw [← this, map_sum, ← Fin.sum_univ_eq_sum_range (fun x => φ (d.u (a * d.q + x) * d.rel (c + x * d.bw))) d.q]
  exact Finset.sum_congr rfl fun x _ => by beta_reduce; rw [map_mul, add_comm (x.val * d.bw)]

theorem data_ech (d : CData) (hd : DataOK d) {B : ℕ} (hB : d.bw = B) :
    EchOK (Emat (fun (a : Fin d.r) (x : Fin d.q) => φ (rowM d.u d.q a x))
      (fun (x : Fin d.q) (c : Fin B) => φ (rowM d.rel d.bw x c))) (pivF d hd hB) (frF d hd hB) := by
  have hd' := hd
  obtain ⟨-, -, -, -, ⟨hl1, hl2, hrk, -, hpl, hpr, hech, -⟩⟩ := hd'
  refine ⟨fun a b => ?_, fun f g hfg => ?_, fun a f h => ?_, fun c => ?_⟩
  · rw [emat_eq φ d hd hB]
    unfold rowM pivF
    simp only
    rw [hech a a.2 b b.2, phi_ite]
    by_cases h : a = b
    · rw [if_pos h, if_pos (congrArg Fin.val h)]
    · rw [if_neg h, if_neg (fun h' => h (Fin.ext h'))]
  · have e := congrArg Fin.val hfg
    simp only [frF] at e
    have h1 := (hpl (d.r + f) (by omega)).2
    have h2 := (hpl (d.r + g) (by omega)).2
    rw [e] at h1
    exact Fin.ext (by omega)
  · have e := congrArg Fin.val h
    simp only [pivF, frF] at e
    have h1 := (hpl a (by omega)).2
    have h2 := (hpl (d.r + f) (by omega)).2
    rw [e] at h1
    omega
  · obtain ⟨ht, hc⟩ := hpr c (hB ▸ c.2)
    by_cases hx : d.tag c < d.r
    · exact Or.inl ⟨⟨d.tag c, hx⟩, Fin.ext (by simp only [pivF]; exact hc)⟩
    · refine Or.inr ⟨⟨d.tag c - d.r, by omega⟩, Fin.ext ?_⟩
      simp only [frF]
      rw [show d.r + (d.tag c - d.r) = d.tag c by omega]
      exact hc

theorem nvec_eq (d : CData) (hd : DataOK d) {B : ℕ} (hB : d.bw = B) (f : Fin d.k) (t : Fin B) :
    nvec (Emat (fun (a : Fin d.r) (x : Fin d.q) => φ (rowM d.u d.q a x))
      (fun (x : Fin d.q) (c : Fin B) => φ (rowM d.rel d.bw x c))) (pivF d hd hB) (frF d hd hB) f t =
      φ (nvalF d.e d.bw d.tag d.r (d.lst (d.r + f)) t) := by
  have hd' := hd
  obtain ⟨-, -, -, -, ⟨hl1, hl2, hrk, -, hpl, hpr, -⟩⟩ := hd'
  unfold nvec nvalF
  rw [map_sub, phi_ite]
  have e1 : (if t = frF d hd hB f then (1 : F) else 0) = if t.val = d.lst (d.r + f) then 1 else 0 := by
    by_cases h : t.val = d.lst (d.r + f)
    · rw [if_pos (Fin.ext h), if_pos h]
    · rw [if_neg (fun h' => h (congrArg Fin.val h')), if_neg h]
  rw [e1]
  congr 1
  simp only [emat_eq φ d hd hB]
  obtain ⟨ht, hc⟩ := hpr t (hB ▸ t.2)
  have key : ∀ a : Fin d.r, (t = pivF d hd hB a) ↔ a.val = d.tag t := by
    intro a
    constructor
    · intro h
      have e := congrArg Fin.val h
      simp only [pivF] at e
      rw [e, (hpl a (by omega)).2]
    · intro h
      exact Fin.ext (by simp only [pivF]; rw [h]; exact hc.symm)
  by_cases hx : d.tag t < d.r
  · rw [if_pos hx]
    rw [Finset.sum_eq_single ⟨d.tag t, hx⟩]
    · rw [if_pos ((key _).2 rfl), mul_one]
      unfold rowM frF
      rfl
    · intro a _ ha
      rw [if_neg (fun h => ha (Fin.ext ((key a).1 h))), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hx, map_zero]
    exact Finset.sum_eq_zero fun a _ => by
      rw [if_neg (fun h => hx (by rw [← (key a).1 h]; exact a.2)), mul_zero]

theorem data_vg (d : CData) (hd : DataOK d) (st : ℕ → ℕ) {A R B : ℕ} (hR : d.rw = R) (hB : d.bw = B) :
    ∃ ents : Fin d.mg → KerEntry d.NG F,
      PreOK₂ (fun (i : Fin A) (t : Fin d.NG) => φ (blockM d.gown d.gw d.glane d.gwl st i t))
        (fun (i : Fin R) (t : Fin d.NG) => φ (colM d.ground d.rw i t))
        (fun (i : Fin B) (t : Fin d.NG) => φ (colM d.gbat d.bw i t)) ents
        (fun (f : Fin d.k) (e : Fin d.mg) => φ (rowM d.yg d.mg f e))
        (fun f => nvec (Emat (fun (a : Fin d.r) (x : Fin d.q) => φ (rowM d.u d.q a x))
          (fun (x : Fin d.q) (c : Fin B) => φ (rowM d.rel d.bw x c))) (pivF d hd hB) (frF d hd hB) f) := by
  have hd' := hd
  obtain ⟨-, -, -, -, ⟨-, -, -, -, -, -, -, hE, hN, hP⟩⟩ := hd'
  refine ⟨fun e => entF φ d.gej d.ges d.gepo d.geco d.gpidx d.gcoef d.NG e (hE e e.2).1
    (fun p hp => ((hE e e.2).2.1 p hp).1), fun e i => ?_, fun e i => ?_, fun f t => ?_⟩
  · rw [kcoord_map φ (blockM d.gown d.gw d.glane d.gwl st), kco_blockM _ _ _ _ _ _ _ _ _ _ _ _ _
      (fun p hp => ((hE e e.2).2.1 p hp).2) (hE e e.2).2.2.1, map_zero]
  · rw [kcoord_map φ (colM d.ground d.rw), kco_colM, (hE e e.2).2.2.2.1 i (hR ▸ i.2), map_zero]
  · have hc : ∀ e : Fin d.mg, kcoord (fun (i : Fin B) (t : Fin d.NG) => φ (colM d.gbat d.bw i t))
        (entF φ d.gej d.ges d.gepo d.geco d.gpidx d.gcoef d.NG e (hE e e.2).1
          (fun p hp => ((hE e e.2).2.1 p hp).1)) t = φ (d.beta (e * d.bw + t)) := by
      intro e
      rw [kcoord_map φ (colM d.gbat d.bw), kco_colM]
      exact congrArg φ ((hE e e.2).2.2.2.2 t (hB ▸ t.2))
    beta_reduce
    rw [nvec_eq φ d hd hB f t, ← hN f f.2 t (hB ▸ t.2)]
    simp only [hc, rowM]
    have := hP f f.2 t (hB ▸ t.2)
    simp only [zero_add] at this
    rw [← this, map_sum, ← Fin.sum_univ_eq_sum_range (fun p => φ (d.yg (f * d.mg + p) * d.beta (t + p * d.bw))) d.mg]
    exact Finset.sum_congr rfl fun p _ => by rw [map_mul, add_comm (p.val * d.bw)]

/-- Lift `l`: the right-inverse Prop. -/
theorem data_lift (d : CData) (hd : DataOK d) (l : ℕ) (hl : l < d.nl) {W : ℕ} (hW : d.lw l = W) :
    RinvOK (fun (i x : Fin W) => φ (d.lo (d.loff l + i * W + x)))
      (fun (x j : Fin W) => φ (d.lu (d.loff l + x * W + j))) := by
  obtain ⟨-, -, hL, -⟩ := hd
  obtain ⟨hp, hid⟩ := hL l hl
  rw [hW] at hp hid
  intro i j
  have h1 := hp i i.2 j j.2
  rw [hid i i.2 j j.2] at h1
  have h2 := congrArg φ h1
  rw [map_sum, phi_ite,
    ← Fin.sum_univ_eq_sum_range (fun p => φ (d.lo (d.loff l + i * W + p) * d.lu (d.loff l + j + p * W))) W]
    at h2
  have eq : (if i = j then (1 : F) else 0) = if i.val = j.val then 1 else 0 := by
    by_cases h : i = j
    · rw [if_pos h, if_pos (congrArg Fin.val h)]
    · rw [if_neg h, if_neg (fun h' => h (Fin.ext h'))]
  beta_reduce
  rw [eq, ← h2]
  exact Finset.sum_congr rfl fun x _ => by
    rw [map_mul, show d.loff l + j + x.val * W = d.loff l + x.val * W + j by ring]

end Field

#print axioms data_ech
#print axioms nvec_eq
#print axioms data_vg
#print axioms data_lift

end R1Z.CertData
