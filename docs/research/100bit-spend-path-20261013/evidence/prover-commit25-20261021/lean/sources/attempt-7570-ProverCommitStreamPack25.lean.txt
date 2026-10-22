import R1Z.ProverCommitPackWindows25
/-! Three search windows share one persistent source counter. Their consumed
prefixes are packed consecutively and their unused words remain in the
bijection as spare suffixes. This closes the fixed-window gap in the local
rejection marginal; it does not identify the full shipped caller. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitStreamPack25
open R0Z R0Z.FsAbort R1Z.CouplingR1PBin
open ProverCommitProduct25 ProverCommitPack25
attribute [local instance] Classical.propDecidable
variable {A : Type} (zero : A)

abbrev Trio (T : Type) := T × (T × T)

def tripleEquiv (k : Nat) : Trio (Fin k → A) ≃ (Fin (k+(k+k)) → A) :=
  (Equiv.prodCongr (Equiv.refl (Fin k → A)) (ProverCommitPackWindows25.equiv zero k k)).trans
    (ProverCommitPackWindows25.equiv zero k (k+k))

theorem triple_uniform [Fintype A] (k : Nat) : MP (tripleEquiv zero k) :=
  mp_equiv (tripleEquiv zero k)

theorem pack_initial {n m : Nat} (a : Fin n → A) (b : Fin m → A)
    (i : Fin n) (before : i.val < used zero a) :
    ProverCommitPackWindows25.pack zero (a,b)
      ⟨i.val,by have h:=i.isLt;omega⟩ = a i := by
  simp only [ProverCommitPackWindows25.pack]
  rw [dif_pos before]

theorem pack_following {n m : Nat} (a : Fin n → A) (b : Fin m → A)
    (i : Fin m) :
    ProverCommitPackWindows25.pack zero (a,b)
      ⟨used zero a+i.val,by have hc:=used_le zero a;have hi:=i.isLt;omega⟩ = b i := by
  simp only [ProverCommitPackWindows25.pack]
  rw [dif_neg (by omega),dif_pos (by have hi:=i.isLt;omega)]
  apply congrArg b
  apply Fin.ext
  simp only [Fin.val_mk]
  omega

/-- The next search starts at the preceding search's actual consumed count.
Every word of the second window is retained at that position. -/
theorem second_window (k : Nat) (a b c : Fin k → A) (i : Fin k)
    (before : i.val < used zero b) :
    tripleEquiv zero k (a,b,c)
      ⟨used zero a+i.val,by have h:=used_le zero a;have hi:=i.isLt;omega⟩ = b i := by
  change ProverCommitPackWindows25.pack zero (a,ProverCommitPackWindows25.pack zero (b,c)) _ = _
  exact (pack_following zero a (ProverCommitPackWindows25.pack zero (b,c))
    (⟨i.val,by have hi:=i.isLt;omega⟩ : Fin (k+k))).trans
      (pack_initial zero b c i before)

theorem third_window (k : Nat) (a b c : Fin k → A) (i : Fin k) :
    tripleEquiv zero k (a,b,c)
      ⟨used zero a+(used zero b+i.val),by
        have h₁:=used_le zero a;have h₂:=used_le zero b;have hi:=i.isLt;omega⟩ = c i := by
  change ProverCommitPackWindows25.pack zero (a,ProverCommitPackWindows25.pack zero (b,c)) _ = _
  exact (pack_following zero a (ProverCommitPackWindows25.pack zero (b,c))
    (⟨used zero b+i.val,by have hc:=used_le zero b;have hi:=i.isLt;omega⟩ : Fin (k+k))).trans
      (pack_following zero b c i)

def separate (k : Nat) : (Trio (NZ zero) × Trio (Fin k → A)) ≃
    Trio (NZ zero × (Fin k → A)) where
  toFun p := ((p.1.1,p.2.1),(p.1.2.1,p.2.2.1),(p.1.2.2,p.2.2.2))
  invFun p := ((p.1.1,p.2.1.1,p.2.2.1),(p.1.2,p.2.1.2,p.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

def raw (k : Nat) (p : Trio (NZ zero) × Trio (Fin k → A)) : Trio (Fin k → A) :=
  ((swap zero k (p.1.1,p.2.1)).2,
   (swap zero k (p.1.2.1,p.2.2.1)).2,
   (swap zero k (p.1.2.2,p.2.2.2)).2)

/-- Model nonzero coins times independent uniform fuel reconstruct a complete
uniform fifteen-word persistent source stream when k=5. -/
theorem source_stream_marginal [Fintype A] [Nonempty (NZ zero)] (k : Nat) :
    MP (fun p => tripleEquiv zero k (raw zero k p)) := by
  have h : MP (fun p : Trio (NZ zero × (Fin k → A)) =>
      ((swap zero k p.1).2,(swap zero k p.2.1).2,(swap zero k p.2.2).2)) :=
    mp_prodMap (raw_marginal zero k) (mp_prodMap (raw_marginal zero k) (raw_marginal zero k))
  intro test
  exact (mp_equiv (separate zero k)
    (fun p => test (tripleEquiv zero k
      ((swap zero k p.1).2,(swap zero k p.2.1).2,(swap zero k p.2.2).2)))).trans
    ((h (fun t => test (tripleEquiv zero k t))).trans (triple_uniform zero k test))

#print axioms triple_uniform
#print axioms pack_initial
#print axioms pack_following
#print axioms second_window
#print axioms third_window
#print axioms source_stream_marginal
end R1Z.ProverCommitStreamPack25
