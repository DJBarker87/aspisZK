import Lean
import NFY_Part032
import NFY_Part033

set_option autoImplicit false
noncomputable section
namespace NGF_NEY_ResultStores
open Aeneas Aeneas.Std Result

def observe {α : Type} (xs : List α) : Nat → Option α := fun k => xs[k]?

theorem copy_observe {α : Type} (dst src : List α) (start : Nat)
    (fits : start+src.length≤dst.length) :
    observe (dst.setSlice! start src) =
      KMX_CopyMeaning.loop (fun j => src[j-start]?) (observe dst) start src.length := by
  funext k
  rw [KMX_CopyMeaning.loop_spec]
  by_cases inside : start≤k ∧ k<start+src.length
  · rw [if_pos inside]
    exact NFY_NEL_CopyArrayLaw.list_inside dst src start k fits inside
  · rw [if_neg inside]
    exact NFY_NEJ_ArrayFrame.list_frame dst src start k fits (by omega)

theorem set_observe {α : Type} (dst : List α) (i : Nat) (value : α)
    (inside : i<dst.length) :
    observe (dst.set i value) = KMX_CopyMeaning.write (observe dst) i (some value) := by
  funext k
  unfold observe KMX_CopyMeaning.write
  by_cases same : k=i
  · subst k
    rw [if_pos rfl,List.getElem?_set_self inside]
  · rw [if_neg same]
    exact List.getElem?_set_ne (Ne.symm same)

def writes (out : Array U8 792#usize) (master selected nullifier : Array U8 32#usize)
    (kind lane : U8) (afterstate : Array U8 688#usize) : Nat → Option U8 :=
  let magic := KMX_CopyMeaning.loop
    (fun j => ([65#u8,83#u8,82#u8,56#u8] : List U8)[j]?) (observe out.val) 0 4
  let version := KMX_CopyMeaning.write magic 4 (some 1#u8)
  let transition := KMX_CopyMeaning.write version 5 (some kind)
  let digestVersion := KMX_CopyMeaning.write transition 6 (some 1#u8)
  let outputLane := KMX_CopyMeaning.write digestVersion 7 (some lane)
  let masterBytes := KMX_CopyMeaning.loop (fun j => master.val[j-8]?) outputLane 8 32
  let selectedBytes := KMX_CopyMeaning.loop (fun j => selected.val[j-40]?) masterBytes 40 32
  let nullifierBytes := KMX_CopyMeaning.loop (fun j => nullifier.val[j-72]?) selectedBytes 72 32
  KMX_CopyMeaning.loop (fun j => afterstate.val[j-104]?) nullifierBytes 104 688

/-- The actual emitted model stores have exactly the nine KMX window laws,
including every byte outside the selected window's footprint. -/
theorem stores_observe (out : Array U8 792#usize) (master selected nullifier : Array U8 32#usize)
    (kind lane : U8) (afterstate : Array U8 688#usize) :
    observe (AspisR1.S2K.ResultEncoding.stores out master selected nullifier kind lane afterstate).val =
      writes out master selected nullifier kind lane afterstate := by
  unfold AspisR1.S2K.ResultEncoding.stores
  simp [writes,copy_observe,set_observe,List.length_setSlice!,List.length_set,
    out.property,master.property,selected.property,nullifier.property,afterstate.property]

#print axioms copy_observe
#print axioms set_observe
#print axioms stores_observe
end NGF_NEY_ResultStores

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
