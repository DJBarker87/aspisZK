import S2W_D189Entry
import PoolS2_Index
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolS2_RawSnapshot
open Aeneas Aeneas.Std Result S2W_D189Entry
abbrev Account := AdapterRw.Cuts.Account

/-- Pool raw-read VALUE view: unlike verifier deferred snapshots, EVERY length
reaches the strict codec. This is computed from ORIGINAL retained buffers.
Native Pool snapshot/borrow/allocation interpretation is not established here. -/
def snapshot (e : Entry) (a : Nat) : Account :=
  let bytes := e.buffers (e.handles a).1
  {(e.records (e.handles a).1).owned with
    length := .Ok (Slice.len bytes), bytes := .Ok bytes}

def accounts (e : Entry) : Slice Account :=
  ⟨List.ofFn (fun a : Fin 12 => snapshot e a.val),by simp; scalar_tac⟩

theorem count (e : Entry) : (accounts e).val.length = 12 := by simp [accounts]

theorem raw (e : Entry) (a : Nat) :
    (snapshot e a).bytes = .Ok (e.buffers (e.handles a).1) ∧
    (snapshot e a).length = .Ok (Slice.len (e.buffers (e.handles a).1)) := ⟨rfl,rfl⟩

theorem metadata (e : Entry) (a : Nat) :
    (snapshot e a).key = (e.records (e.handles a).1).owned.key ∧
    (snapshot e a).owner = (e.records (e.handles a).1).owned.owner ∧
    (snapshot e a).is_signer = (e.records (e.handles a).1).owned.is_signer ∧
    (snapshot e a).is_writable = (e.records (e.handles a).1).owned.is_writable ∧
    (snapshot e a).executable = (e.records (e.handles a).1).owned.executable :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem indexed (e : Entry) (a : Usize) (within : a.val < 12) :
    Slice.index_usize (accounts e) a = ok (snapshot e a.val) := by
  have bound : a.val < (accounts e).val.length := by simpa only [count] using within
  rw [PoolS2_Index.read (accounts e) a bound]
  congr 1
  change (List.ofFn (fun x : Fin 12 => snapshot e x.val))[a.val] = snapshot e a.val
  simp only [List.getElem_ofFn]

theorem cell_alias (e : Entry) (a b : Nat) (same : (e.handles a).1 = (e.handles b).1) :
    snapshot e a = snapshot e b := by simp [snapshot,same]

#print axioms count
#print axioms raw
#print axioms metadata
#print axioms indexed
#print axioms cell_alias
end AspisR1.PoolS2_RawSnapshot
end
