import AspisV8R17.ContextShear

/-! Ideal finite-coin transport for the three source correction blocks.
The observation equations are required for EVERY coin vector at a fixed
prefix. This does not establish their source premises, a seed law, or an
adaptive-prefix coupling. No resampling of previously used coins occurs. -/
set_option autoImplicit false
namespace AspisV8R17
variable {C H G A B D S : Type*}
  [AddCommGroup C] [AddCommGroup H] [AddCommGroup G]
  [AddCommGroup D] [AddCommGroup S]

def witnessShear (dc : C) (dh : C → H) (dg : C → H → G) :
    C × H × G ≃ C × H × G where
  toFun x := (x.1 + dc, x.2.1 + dh x.1, x.2.2 + dg x.1 x.2.1)
  invFun y := (y.1 - dc, y.2.1 - dh (y.1 - dc),
    y.2.2 - dg (y.1 - dc) (y.2.1 - dh (y.1 - dc)))
  left_inv x := by rcases x with ⟨c,h,g⟩; simp
  right_inv y := by rcases y with ⟨c,h,g⟩; simp

def witnessObservation (cv : C → A) (hv : C → H → B)
    (gv : G →+ D) (gs : G →+ S) (shared : C → H → S)
    (x : C × H × G) : A × B × D × S :=
  (cv x.1, hv x.1 x.2.1, gv x.2.2, shared x.1 x.2.1 + gs x.2.2)

theorem witness_shear_commutes
    (cl cr : C → A) (hl hr : C → H → B)
    (gv : G →+ D) (gs : G →+ S) (sl sr : C → H → S)
    (dc : C) (dh : C → H) (dg : C → H → G)
    (hc : ∀ c, cr (c + dc) = cl c)
    (hh : ∀ c h, hr (c + dc) (h + dh c) = hl c h)
    (hg : ∀ c h, gv (dg c h) = 0)
    (hs : ∀ c h, gs (dg c h) = sl c h - sr (c + dc) (h + dh c))
    (x : C × H × G) :
    witnessObservation cr hr gv gs sr (witnessShear dc dh dg x) =
      witnessObservation cl hl gv gs sl x := by
  rcases x with ⟨c,h,g⟩
  apply Prod.ext
  · exact hc c
  · apply Prod.ext
    · exact hh c h
    · apply Prod.ext
      · change gv (g + dg c h) = gv g
        rw [map_add, hg, add_zero]
      · change sr (c + dc) (h + dh c) + gs (g + dg c h) = sl c h + gs g
        rw [map_add, hs]
        abel

theorem witness_shear_same_uniform_law [Fintype C] [Fintype H] [Fintype G]
    (cl cr : C → A) (hl hr : C → H → B)
    (gv : G →+ D) (gs : G →+ S) (sl sr : C → H → S)
    (dc : C) (dh : C → H) (dg : C → H → G)
    (hc : ∀ c, cr (c + dc) = cl c)
    (hh : ∀ c h, hr (c + dc) (h + dh c) = hl c h)
    (hg : ∀ c h, gv (dg c h) = 0)
    (hs : ∀ c h, gs (dg c h) = sl c h - sr (c + dc) (h + dh c)) :
    AspisV8H1C2.SameUniformLaw
      (witnessObservation cl hl gv gs sl) (witnessObservation cr hr gv gs sr) := by
  exact AspisV8H1C2.sameUniformLaw_of_equiv _ _ (witnessShear dc dh dg)
    (witness_shear_commutes cl cr hl hr gv gs sl sr dc dh dg hc hh hg hs)

#print axioms witnessShear
#print axioms witness_shear_commutes
#print axioms witness_shear_same_uniform_law
end AspisV8R17
