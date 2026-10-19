import CuSavingsArrayStorage

/-! Complete emitted infallible array construction versus the ordered callback
builder. The equation is under the explicit primitive/library interpretation;
experimental frontend normalization admission remains a separate obligation. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace AspisR1.CuSavingsArraySourceBuilder
open Aeneas Aeneas.Std Result
open CuSavingsArrayGraphLoop CuSavingsArrayFillCells CuSavingsArrayStorage CuSavingsArrayBuilder

abbrev sourceErased {T F : Type} (inst : core.ops.function.FnMut F Usize T) :=
  AspisR1CuArrayGraph.core.array.try_from_fn_erased (CuSavingsTryGraphRuntime.neverTry T) inst

theorem erased_eq_cells {T F : Type} (inst : core.ops.function.FnMut F Usize T)
    (n : Nat) (state : F) (buffer : Slice (Option T)) (hlen : buffer.length = n) :
    sourceErased inst buffer state = (do
      let (values,_) ← cells inst n 0#usize state
      .ok (.Continue (),store buffer 0 values.val)) := by
  unfold sourceErased AspisR1CuArrayGraph.core.array.try_from_fn_erased
  change sourceLoop inst (fun s => s) state buffer 0#usize = _
  trans (do
    let final ← fill inst n state buffer 0#usize
    .ok (.Continue (),final))
  · exact source_eq_fill inst n (fun s => s) state buffer 0#usize (by simpa using hlen.symm)
  rw [fill_eq_cells]
  cases hc : cells inst n 0#usize state with
  | fail e => rfl
  | div => rfl
  | ok pair => rcases pair with ⟨values,state1⟩;rfl

theorem assume_init_store {T : Type} {N : Usize} (array : Array (Option T) N)
    (values : List T) (hlen : values.length = N.val) :
    AspisR1CuArrayGraph.core.mem.maybe_uninit.MaybeUninit.array_assume_init
      (Array.from_slice array (store array.to_slice 0 values)) = .ok ⟨values,hlen⟩ := by
  have hb : array.to_slice.length = values.length := by
    change array.val.length = values.length
    rw [array.property,hlen]
  have hs : (store array.to_slice 0 values).val.length = N.val := by
    change (store array.to_slice 0 values).length = N.val
    rw [store_length]
    exact array.property
  have hval : (Array.from_slice array (store array.to_slice 0 values)).val = values.map some :=
    (Array.from_slice_val _ _ hs).trans (store_all values array.to_slice hb)
  have hv : values.length = (Array.from_slice array (store array.to_slice 0 values)).val.length := by
    rw [hval,List.length_map]
  have hinit : AspisR1CuArrayGraph.initializedCells
      (Array.from_slice array (store array.to_slice 0 values)).val = .ok ⟨values,hv⟩ := by
    have aux (xs : List (Option T)) (heq : xs = values.map some)
        (hp : values.length = xs.length) :
        AspisR1CuArrayGraph.initializedCells xs = .ok ⟨values,hp⟩ := by
      subst xs
      exact initialized_map values
    exact aux _ hval hv
  unfold AspisR1CuArrayGraph.core.mem.maybe_uninit.MaybeUninit.array_assume_init
  simp only [hinit,bind_tc_ok]

theorem try_eq_build {T F : Type} (N : Usize) (inst : core.ops.function.FnMut F Usize T)
    (state : F) :
    AspisR1CuArrayGraph.core.array.try_from_fn (CuSavingsTryGraphRuntime.neverTry T)
      (CuSavingsTryGraphRuntime.neverResidual (Array T N)) inst state = build N inst state := by
  let array : Array (Option T) N := Array.repeat N none
  have hl : array.to_slice.length = N.val := array.property
  unfold AspisR1CuArrayGraph.core.array.try_from_fn
  simp only [AspisR1CuArrayGraph.core.mem.maybe_uninit.MaybeUninit.uninit,bind_tc_ok,Array.to_slice_mut,lift]
  dsimp only [CuSavingsTryGraphRuntime.neverTry,
    AspisR1CuArrayGraph.core.mem.maybe_uninit.MaybeUninit,Prod.casesOn,
    CuSavingsTryGraphRuntime.neverResidual,CuSavingsTryGraphRuntime.Residual.TryInst]
  dsimp only
  change (do
    let (cf,s) ← sourceErased inst array.to_slice state
    match cf with
    | .Continue _ => do
      let a ← AspisR1CuArrayGraph.core.mem.maybe_uninit.MaybeUninit.array_assume_init
        (Array.from_slice array s)
      (CuSavingsTryGraphRuntime.neverResidual (Array T N)).TryInst.from_output a
    | .Break r => (CuSavingsTryGraphRuntime.neverResidual (Array T N)).TryInst.FromResidualInst.from_residual r) =
      build N inst state
  rw [erased_eq_cells inst N.val state array.to_slice hl]
  unfold build
  cases hc : cells inst N.val 0#usize state with
  | fail e => rfl
  | div => rfl
  | ok pair =>
    rcases pair with ⟨values,state1⟩
    simp only [bind_tc_ok]
    change (do
      let a ← AspisR1CuArrayGraph.core.mem.maybe_uninit.MaybeUninit.array_assume_init
        (Array.from_slice array (store array.to_slice 0 values.val))
      (CuSavingsTryGraphRuntime.neverResidual (Array T N)).TryInst.from_output a) =
        .ok ⟨values.val,values.property⟩
    rw [assume_init_store array values.val values.property]
    rfl

#print axioms erased_eq_cells
#print axioms assume_init_store
#print axioms try_eq_build
end AspisR1.CuSavingsArraySourceBuilder
