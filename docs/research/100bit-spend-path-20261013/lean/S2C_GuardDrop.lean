import S2C_CopyRegions
set_option autoImplicit false
namespace AspisR1.S2C
open S2Trust

/-- A library match can only select the already-fixed next cut. This rules out
joining a successful library run unrelated to the caller's continuation. -/
theorem fixed_cut {W F : Type} (L : Library W F) (before after : W)
    (op : Op) (expected : Heap F) (reply : Reply)
    (actual : L.run before op = (after, reply))
    (matched : Matches L before op (expected,reply)) : L.related after expected := by
  obtain ⟨next,run,related⟩ := matched
  have eq := Prod.mk.inj (actual.symm.trans run)
  exact eq.1 ▸ related

/-- Per shared guard Drop on a fixed execution cut, using only shared_drop.
The counter bound and lookup must come from that cut's admission. -/
theorem shared_drop_cut {E W F : Type} (L : Library W F)
    (trust : S2TrustedSdkBorrow L) (native : E → Nat → W)
    (e : E) (k : Nat) (s : Heap F) (g : Guard)
    (related : L.related (native e k) s) (valid : Valid s)
    (found : lookup s g.token = some g) (kind : g.kind = .shared)
    (positive : 0 < s.counter g.cell)
    (actual : L.run (native e k) (.drop g.token) = (native e (k+1), .unit)) :
    L.related (native e (k+1)) (release s g) :=
  fixed_cut L _ _ _ _ _ actual
    (trust.shared_drop _ _ _ _ related valid found kind positive)

theorem exclusive_drop_cut {E W F : Type} (L : Library W F)
    (trust : S2TrustedSdkBorrow L) (native : E → Nat → W)
    (e : E) (k : Nat) (s : Heap F) (g : Guard)
    (related : L.related (native e k) s) (valid : Valid s)
    (found : lookup s g.token = some g) (kind : g.kind = .exclusive)
    (exclusive : s.counter g.cell = -1)
    (actual : L.run (native e k) (.drop g.token) = (native e (k+1), .unit)) :
    L.related (native e (k+1)) (release s g) :=
  fixed_cut L _ _ _ _ _ actual
    (trust.exclusive_drop _ _ _ _ related valid found kind exclusive)

/-- No guard Drop writes payload, metadata, lamports, Rc, or allocator state.
This is the exact release transition in the adopted trust interface. -/
theorem release_frame {F : Type} (s : Heap F) (g : Guard) :
    (release s g).accounts = s.accounts ∧
    (release s g).ownerLive = s.ownerLive ∧
    (release s g).allocated = s.allocated ∧
    (release s g).payload = s.payload ∧
    (release s g).external = s.external ∧
    (release s g).ambient = s.ambient := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem release_counter {F : Type} (s : Heap F) (g : Guard) (c : Nat) :
    (release s g).counter c = if c = g.cell then
      (if g.kind = .shared then s.counter c - 1 else 0) else s.counter c := by
  by_cases eq : c = g.cell
  · subst c; simp only [release,put,eq_self_iff_true,ite_true]
  · simp only [release,put,if_neg eq]

/-- The final native observations are of the same chosen successor, not a
separate success witness. No injectivity of the interpretation is needed. -/
theorem drop_native_payload {W F : Type} (L : Library W F)
    (trust : S2TrustedSdkBorrow L) (after : W) (s : Heap F) (g : Guard)
    (related : L.related after (release s g)) (valid : Valid (release s g))
    (c : Nat) : L.cellPayload after c = s.payload c :=
  trust.cell_payload _ _ related valid c

#print axioms fixed_cut
#print axioms shared_drop_cut
#print axioms exclusive_drop_cut
#print axioms release_frame
#print axioms release_counter
#print axioms drop_native_payload
end AspisR1.S2C
