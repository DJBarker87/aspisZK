import R0Z.BuilderWitnessTrace
import R0Z.WriterRefineMerge
import R0Z.M31Prime

/-! The witness-level copy builder with the bank merge (DESIGN-BUILDER-MODEL §13 (2)).

As in pair_trace.rs, the 20 append blocks (34..53, rows 544..863) are written
into a separate late bank and every other row into the stable bank; the
extracted `merge_check` / `merge_copy` (pair_forest_trace.rs:281-314) combine
them.  Both banks are 16 x 1024 column-major (index = column * 1024 + row).
`builder_witness_merged`: the shape check passes, the merge returns `ok`, and
every cell of the merged trace (columns 16..28 zero) lifts to
`buildModel pub (toModel W)`.  `Nat.Prime 2147483647` is now `R0Z.m31_prime`. -/
set_option autoImplicit false
noncomputable section

namespace R0Z.WriterRefine
open Aeneas Aeneas.Std Result
open R0Z.BuilderModel

theorem n16384 : (16384#usize : Usize).val = 16384 := by simp

def arrT (f : Fin 16384 → U32) : Array U32 16384#usize :=
  ⟨List.ofFn f, by rw [List.length_ofFn]; exact n16384.symm⟩

theorem arrT_val (f : Fin 16384 → U32) : (arrT f).val = List.ofFn f := by rw [arrT]

theorem arrT_get (f : Fin 16384 → U32) (i : Nat) (h : i < 16384) : (arrT f).val[i]! = f ⟨i, h⟩ := by
  rw [arrT_val, List.getElem!_eq_getElem?_getD, List.getElem?_ofFn, dif_pos h]
  exact Option.getD_some

/-- The unmerged cell table, column-major. -/
def cellT (W : RustWitness) (P : RustPublic) (k : Fin 16384) : U32 :=
  copyCell W P ⟨k.val / 1024, by omega⟩ ⟨k.val % 1024, Nat.mod_lt _ (by omega)⟩

/-- The stable bank: every row outside 544..863. -/
def stableBank (W : RustWitness) (P : RustPublic) : Array U32 16384#usize :=
  arrT (fun k => if LateRow k.val then 0#u32 else cellT W P k)

/-- The late bank: the append blocks 34..53 in rows 544..863, zero elsewhere. -/
def lateBank (W : RustWitness) (P : RustPublic) : Array U32 16384#usize :=
  arrT (fun k => if LateRow k.val then
      (blockR W P (k.val % 1024 / 16)).val[(k.val % 1024 % 16) * 16 + k.val / 1024]!
    else 0#u32)

def mergedR (W : RustWitness) (P : RustPublic) : Result (Array U32 16384#usize) :=
  R0WriterCopies.merge_copy (stableBank W P) (lateBank W P)

/-- **The merged copy trace** (29 x 1024). -/
def copyCellMerged (W : RustWitness) (P : RustPublic) (c : Fin 29) (r : Fin 1024) : U32 :=
  if c.val < 16 then (okOr (mergedR W P) (Array.repeat 16384#usize 0#u32)).val[c.val * 1024 + r.val]!
  else 0#u32

variable {K : Type} [Field K] [CharP K 0x7fffffff]

theorem builder_witness_merged (W : RustWitness) (P : RustPublic) (pub : R0P.Public K)
    (hP : PubCorr P pub) (hW : WitnessOk W) :
    R0WriterCopies.merge_check (stableBank W P) (lateBank W P) = ok true ∧
    (∃ out, mergedR W P = ok out) ∧
    (∀ h : Fin 57, ∃ b, RustWriterChain P.variant (rustChunks W P) h.val = ok b) ∧
    (∃ pb, pathR W P = ok pb) ∧ (∃ ab, auxR W P = ok ab) ∧
    ∀ (c : Fin 29) (r : Fin 1024),
      liftU (K := K) (copyCellMerged W P c r) = buildModel pub (toModel W) c r := by
  obtain ⟨hblk, hpath, haux, hcell⟩ := builder_witness_model W P pub hP hW R0Z.m31_prime
  let M : Nat → U32 := fun k => if h : k < 16384 then cellT W P ⟨k, h⟩ else 0#u32
  have hs : ∀ k, k < 16384 → (stableBank W P).val[k]! = if LateRow k then 0#u32 else M k := by
    intro k hk
    rw [stableBank, arrT_get _ k hk]
    show (if LateRow k then 0#u32 else cellT W P ⟨k, hk⟩) = if LateRow k then 0#u32 else
      (if h : k < 16384 then cellT W P ⟨k, h⟩ else 0#u32)
    rw [dif_pos hk]
  have hl : ∀ k, k < 16384 → (lateBank W P).val[k]! = if LateRow k then M k else 0#u32 := by
    intro k hk
    rw [lateBank, arrT_get _ k hk]
    show (if LateRow k then _ else 0#u32) = if LateRow k then
      (if h : k < 16384 then cellT W P ⟨k, h⟩ else 0#u32) else 0#u32
    rw [dif_pos hk]
    by_cases hr : LateRow k
    · rw [if_pos hr, if_pos hr]
      unfold LateRow at hr
      unfold cellT copyCell
      dsimp only
      rw [if_pos (show k / 1024 < 16 by omega), if_pos (show k % 1024 < 912 by omega)]
    · rw [if_neg hr, if_neg hr]
  obtain ⟨hchk, out, hout, houtv⟩ := merge_model M (stableBank W P) (lateBank W P) hs hl
  refine ⟨hchk, ⟨out, hout⟩, hblk, hpath, haux, fun c r => ?_⟩
  by_cases hc : c.val < 16
  · have hk : c.val * 1024 + r.val < 16384 := by have := r.isLt; omega
    have e : copyCellMerged W P c r = cellT W P ⟨c.val * 1024 + r.val, hk⟩ := by
      unfold copyCellMerged
      rw [if_pos hc, show mergedR W P = ok out from hout, okOr_ok, houtv _ hk]
      show (if h : c.val * 1024 + r.val < 16384 then cellT W P ⟨_, h⟩ else 0#u32) = _
      rw [dif_pos hk]
    rw [e]
    have e2 : cellT W P ⟨c.val * 1024 + r.val, hk⟩ = copyCell W P c r := by
      unfold cellT
      have h1 : (⟨(c.val * 1024 + r.val) / 1024, by omega⟩ : Fin 29) = c := Fin.ext (by show (c.val * 1024 + r.val) / 1024 = c.val; have := r.isLt; omega)
      have h2 : (⟨(c.val * 1024 + r.val) % 1024, Nat.mod_lt _ (by omega)⟩ : Fin 1024) = r :=
        Fin.ext (by show (c.val * 1024 + r.val) % 1024 = r.val; have := r.isLt; omega)
      rw [h1, h2]
    rw [e2]
    exact hcell c r
  · have e : copyCellMerged W P c r = copyCell W P c r := by
      unfold copyCellMerged copyCell
      rw [if_neg hc, if_neg hc]
    rw [e]
    exact hcell c r

#print axioms R0Z.WriterRefine.builder_witness_merged
end R0Z.WriterRefine
