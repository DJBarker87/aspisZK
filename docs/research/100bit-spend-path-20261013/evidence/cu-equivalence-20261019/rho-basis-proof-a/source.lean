import AspisR1RhoBasis.Funs
import ExtractedCurrentReducer
import CuSavingsLoopInvariant
import CuSavingsRhoInputs

/-! Every successful execution of the complete emitted common basis prefix
returns only canonical base-field words. No node/length/termination premise
is assumed: failures and divergence remain part of the original computation.
-/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoBasis
open Aeneas Aeneas.Std Result ControlFlow AspisR1RhoBasis
open AspisV8R17.RawReducer
abbrev Basis := Array U32 256#usize
abbrev Range := core.ops.range.Range Usize

def Good (basis : Basis) : Prop :=
  ∀ (i : Nat) (hi : i < basis.val.length),(basis.val[i]'hi).val < P

private theorem bind_ok {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let x ← m;f x) = .ok out) :
    ∃ x,m = .ok x ∧ f x = .ok out := by
  cases m with
  | fail e => cases h
  | div => cases h
  | ok x => exact ⟨x,rfl,h⟩

theorem mul_canonical (x y out : U32) (h : field.M31.mul x y = .ok out) : out.val < P := by
  obtain ⟨z,hz,_,hc⟩ := ExtractedCurrentReducer.current_mul_mod x y
  have heq := Result.ok.inj (hz.symm.trans h)
  exact heq ▸ hc

theorem good_set (basis : Basis) (index : Usize) (value : U32)
    (hg : Good basis) (hv : value.val < P) : Good (basis.set index value) := by
  intro i hi
  have hi0 : i < basis.val.length := by simpa only [Array.set_val_eq,List.length_set] using hi
  simp only [Array.set_val_eq,List.getElem_set]
  split
  · exact hv
  · exact hg i hi0

theorem good_update (basis out : Basis) (index : Usize) (value : U32)
    (hg : Good basis) (hv : value.val < P)
    (h : Array.update basis index value = .ok out) : Good out := by
  have heq : out = basis.set index value := by
    unfold Array.update at h
    split at h
    · cases h
    · have ho := Result.ok.inj h
      exact ho.symm
  rw [heq]
  exact good_set basis index value hg hv

theorem inner_body (node : U32) (n : Usize) (iter : Range) (basis : Basis)
    (hg : Good basis)
    (out : ControlFlow (Range × Basis) Basis)
    (h : basis_loop0_loop0.body node n iter basis = .ok out) :
    match out with
    | .cont next => Good next.2
    | .done result => Good result := by
  unfold basis_loop0_loop0.body at h
  obtain ⟨pair,_,h⟩ := bind_ok _ _ _ h
  rcases pair with ⟨option,iter1⟩
  simp only [uncurry_apply_pair] at h
  cases option with
  | none => cases Result.ok.inj h;exact hg
  | some index =>
    obtain ⟨word,_,h⟩ := bind_ok _ _ _ h
    obtain ⟨product,hmul,h⟩ := bind_ok _ _ _ h
    obtain ⟨target,_,h⟩ := bind_ok _ _ _ h
    obtain ⟨updated,hupdate,h⟩ := bind_ok _ _ _ h
    cases Result.ok.inj h
    exact good_update basis updated target product hg (mul_canonical word node product hmul) hupdate

theorem inner_success (iter : Range) (node : U32) (basis : Basis) (n : Usize)
    (hg : Good basis) (out : Basis)
    (h : basis_loop0_loop0 iter node basis n = .ok out) : Good out := by
  unfold basis_loop0_loop0 at h
  exact CuSavingsLoopInvariant.success
    (fun pair : Range × Basis => basis_loop0_loop0.body node n pair.1 pair.2)
    (fun pair => Good pair.2) Good
    (by intro pair hp control hcontrol;exact inner_body node n pair.1 pair.2 hp control hcontrol)
    (iter,basis) hg out h

theorem outer_body (length : Usize) (node : U32) (basis : Basis) (n : Usize)
    (hg : Good basis)
    (out : ControlFlow (U32 × Basis × Usize) Basis)
    (h : basis_loop0.body length node basis n = .ok out) :
    match out with
    | .cont next => Good next.2.1
    | .done result => Good result := by
  unfold basis_loop0.body at h
  split at h
  · obtain ⟨updated,hinner,h⟩ := bind_ok _ _ _ h
    have hgood := inner_success _ node basis n hg updated hinner
    obtain ⟨_,_,h⟩ := bind_ok _ _ _ h
    obtain ⟨_,_,h⟩ := bind_ok _ _ _ h
    obtain ⟨_,_,h⟩ := bind_ok _ _ _ h
    obtain ⟨_,_,h⟩ := bind_ok _ _ _ h
    cases Result.ok.inj h
    exact hgood
  · cases Result.ok.inj h;exact hg

theorem outer_success (length : Usize) (node : U32) (basis : Basis) (n : Usize)
    (hg : Good basis) (out : Basis)
    (h : basis_loop0 length node basis n = .ok out) : Good out := by
  unfold basis_loop0 at h
  exact CuSavingsLoopInvariant.success
    (fun state : U32 × Basis × Usize => basis_loop0.body length state.1 state.2.1 state.2.2)
    (fun state => Good state.2.1) Good
    (by intro state hs control hcontrol;exact outer_body length state.1 state.2.1 state.2.2 hs control hcontrol)
    (node,basis,n) hg out h

theorem repeat_good : Good (Array.repeat 256#usize field.M31.ZERO) := by
  intro i hi
  simp only [Array.repeat,List.getElem_replicate]
  rw [field.M31.ZERO]
  have hz : (0#u32).val=0 := by scalar_tac
  rw [hz]
  decide

theorem source_success (length : Usize) (node : U32) (out : Basis)
    (h : basis length node = .ok out) : Good out := by
  unfold basis at h
  obtain ⟨initial,hinit,houter⟩ := bind_ok _ _ _ h
  have hone : field.M31.ONE.val < P := by
    rw [field.M31.ONE]
    have ho : (1#u32).val=1 := by scalar_tac
    rw [ho]
    decide
  have hi := good_update _ initial _ _ repeat_good hone hinit
  exact outer_success length node initial 1#usize hi out houter

theorem input_admitted (length : Usize) (node : U32) (out : Basis)
    (power : AspisR1CuRho.field.QM31) (hlen : length.val ≤ 256)
    (hp : CuSavingsRhoInitRow.Canonical power) (h : basis length node = .ok out) :
    CuSavingsRhoBatches.Admitted
      {power:=power,items:=CuSavingsRhoInputs.items out length hlen} length.val := by
  apply CuSavingsRhoInputs.input_admitted power out length hlen hp
  intro i
  exact source_success length node out h i.val _

#print axioms inner_success
#print axioms outer_success
#print axioms source_success
#print axioms input_admitted
end AspisR1.CuSavingsRhoBasis
