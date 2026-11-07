import NMK_Domain
import NLP_RootCodec
set_option autoImplicit false
noncomputable section
namespace NMK_RootWindow
open Aeneas Aeneas.Std AspisR1
open AspisV8R19.SqueezeOracleBridge
/-- The raw-byte state codec is bijective. At the reached proof extent the
closed Root0 input clause is exactly a32-byte window equality, with no field
canonicality condition, hash injectivity, or successful child premise. -/
theorem root0_iff (checkpoint proof : Slice U8) (length : proof.val.length = 57607) :
 NLP_InputDomain.Root0 checkpoint proof ↔
 (checkpoint.val.drop 112).take 32 = (proof.val.drop 16).take 32 := by
 let root : Array U8 32#usize := ⟨(proof.val.drop 16).take 32, by simp [length]⟩
 have window : OraclePortCompactDraft.slice (MultiproofConeCanonical.bytesOf proof.val) 16 32 =
   MultiproofConeCanonical.bytesOf root.val := by
  simp [OraclePortCompactDraft.slice, MultiproofConeCanonical.bytesOf, root,
   List.map_take, List.map_drop]
 unfold NLP_InputDomain.Root0
 rw [window, NLP_RootCodec.decode_array]
/-- Scalar byte checks used by the native cut, at every position in the window. -/
theorem pointwise (checkpoint proof : Slice U8) (length : proof.val.length = 57607) :
 NLP_InputDomain.Root0 checkpoint proof ↔
 ∀ i : Nat, i < 32 → checkpoint.val[112+i]? = proof.val[16+i]? := by
 rw [root0_iff checkpoint proof length]
 constructor
 · intro same i hi
   have h := congrArg (fun xs : List U8 => xs[i]?) same
   simpa [List.getElem?_take, List.getElem?_drop, hi, Nat.add_comm] using h
 · intro same
   apply List.ext_getElem?
   intro i
   by_cases hi : i < 32
   · simpa [List.getElem?_take, List.getElem?_drop, hi, Nat.add_comm] using same i hi
   · simp [List.getElem?_take, hi]
/-- The minimum Rust slice extent follows from Root0 itself. -/
theorem checkpoint_extent (checkpoint proof : Slice U8) (length : proof.val.length = 57607)
 (root : NLP_InputDomain.Root0 checkpoint proof) : 144 ≤ checkpoint.val.length := by
 have same := (root0_iff checkpoint proof length).mp root
 have counts := congrArg List.length same
 simp only [List.length_take, List.length_drop] at counts
 rw [length] at counts
 omega
#print checkpoint_extent
#print axioms checkpoint_extent
#print pointwise
#print axioms pointwise
#print root0_iff
#print axioms root0_iff
end NMK_RootWindow
