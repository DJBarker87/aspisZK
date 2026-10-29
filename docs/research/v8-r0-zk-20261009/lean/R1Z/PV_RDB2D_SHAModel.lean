import R1Z.PV_RDB2D_ProverRwFullExternalFuns
import Aeneas

section
-- Exact unchanged source component: R1Z.PV_CBL_ShaPadFixed
-- Exact extracted fixed-size safe padding reference; Types empty.
open Aeneas Aeneas.Std Result ControlFlow Error
namespace PV_CBL_ShaPadFixed
/-- [pv_cblib_source::sha_pad_zero]: loop body 0:
    Source: 'lib.rs', lines 423:4-423:34
    Visibility: public -/
@[rust_loop_body]
def sha_pad_zero_loop.body
  (buffer : Array Std.U8 64#usize) (i : Std.Usize) :
  Result (ControlFlow ((Array Std.U8 64#usize) × Std.Usize) (Array Std.U8
    64#usize))
  := do
  if i < 64#usize
  then
    let buffer1 ← Array.update buffer i 0#u8
    let i1 ← lift (Std.Usize.wrapping_add i 1#usize)
    ok (cont (buffer1, i1))
  else ok (done buffer)

/-- [pv_cblib_source::sha_pad_zero]: loop 0:
    Source: 'lib.rs', lines 423:4-423:34
    Visibility: public -/
@[rust_loop]
def sha_pad_zero_loop
  (buffer : Array Std.U8 64#usize) (i : Std.Usize) :
  Result (Array Std.U8 64#usize)
  := do
  loop
    (fun (buffer1, i1) => sha_pad_zero_loop.body buffer1 i1)
    (buffer, i)

/-- [pv_cblib_source::sha_pad_zero]:
    Source: 'lib.rs', lines 420:0-425:1
    Visibility: public -/
def sha_pad_zero
  (buffer : Array Std.U8 64#usize) (pos : Std.Usize) :
  Result (Array Std.U8 64#usize)
  := do
  let buffer1 ← Array.update buffer pos 128#u8
  let i ← lift (Std.Usize.wrapping_add pos 1#usize)
  sha_pad_zero_loop buffer1 i

/-- [pv_cblib_source::sha_pad_suffix8]:
    Source: 'lib.rs', lines 443:0-448:1
    Visibility: public -/
def sha_pad_suffix8
  (buffer : Array Std.U8 64#usize) (suffix : Array Std.U8 8#usize) :
  Result (Array Std.U8 64#usize)
  := do
  let a ← Array.index_usize suffix 0#usize
  let b ← Array.index_usize suffix 1#usize
  let c ← Array.index_usize suffix 2#usize
  let d ← Array.index_usize suffix 3#usize
  let e ← Array.index_usize suffix 4#usize
  let f ← Array.index_usize suffix 5#usize
  let g ← Array.index_usize suffix 6#usize
  let h ← Array.index_usize suffix 7#usize
  let buffer1 ← Array.update buffer 56#usize a
  let buffer2 ← Array.update buffer1 57#usize b
  let buffer3 ← Array.update buffer2 58#usize c
  let buffer4 ← Array.update buffer3 59#usize d
  let buffer5 ← Array.update buffer4 60#usize e
  let buffer6 ← Array.update buffer5 61#usize f
  let buffer7 ← Array.update buffer6 62#usize g
  Array.update buffer7 63#usize h

/-- [pv_cblib_source::sha_pad_owned_split8]:
    Source: 'lib.rs', lines 449:0-459:1
    Visibility: public -/
def sha_pad_owned_split8
  (buffer : Array Std.U8 64#usize) (pos : Std.Usize)
  (suffix : Array Std.U8 8#usize) :
  Result ((Array Std.U8 64#usize) × (Option (Array Std.U8 64#usize)) × (Array
    Std.U8 64#usize) × Std.Usize)
  := do
  let head ← sha_pad_zero buffer pos
  let i ← lift (Std.Usize.wrapping_sub 64#usize pos)
  let i1 ← lift (Std.Usize.wrapping_sub i 1#usize)
  if i1 < 8#usize
  then
    let a := Array.repeat 64#usize 0#u8
    let second ← sha_pad_suffix8 a suffix
    ok (head, some second, head, 0#usize)
  else
    let first ← sha_pad_suffix8 head suffix
    ok (first, none, first, 0#usize)

#print axioms sha_pad_zero_loop.body
#print axioms sha_pad_zero_loop
#print axioms sha_pad_zero
#print axioms sha_pad_suffix8
#print axioms sha_pad_owned_split8
end PV_CBL_ShaPadFixed

end

section
-- Exact unchanged source component: R1Z.PV_CBL_ArrayKernel
-- Generic copy kernel retained verbatim from the successful Aeneas extraction.
open Aeneas Aeneas.Std Result ControlFlow Error
namespace PV_CBL_ArrayKernel
/-- [pv_cblib_source::array_reference]: loop body 0:
    Source: 'lib.rs', lines 38:4-38:36
    Visibility: public -/
@[rust_loop_body]
def array_reference_loop.body
  {T : Type} {N : Std.Usize} (v : Slice T) (out : Array T N) (i : Std.Usize) :
  Result (ControlFlow ((Array T N) × Std.Usize) (Array T N))
  := do
  if i < N
  then
    let t ← Slice.index_usize v i
    let out1 ← Array.update out i t
    let i1 ← lift (Std.Usize.wrapping_add i 1#usize)
    ok (cont (out1, i1))
  else ok (done out)

/-- [pv_cblib_source::array_reference]: loop 0:
    Source: 'lib.rs', lines 38:4-38:36
    Visibility: public -/
@[rust_loop]
def array_reference_loop
  {T : Type} {N : Std.Usize} (v : Slice T) (out : Array T N) (i : Std.Usize) :
  Result (Array T N)
  := do
  loop
    (fun (out1, i1) => array_reference_loop.body v out1 i1)
    (out, i)

/-- [pv_cblib_source::array_reference]:
    Source: 'lib.rs', lines 34:0-40:1
    Visibility: public -/
def array_reference
  {T : Type} (N : Std.Usize) (coremarkerCopyInst : core.marker.Copy T)
  (v : Slice T) (zero : T) :
  Result (Option (Array T N))
  := do
  let i := Slice.len v
  if i != N
  then ok none
  else
    let out := Array.repeat N zero
    let out1 ← array_reference_loop v out 0#usize
    ok (some out1)


#print axioms array_reference_loop.body
#print axioms array_reference_loop
#print axioms array_reference
end PV_CBL_ArrayKernel

end

section
-- Exact unchanged source component: R1Z.PV_CBL_ArrayStep
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_CBL_ArrayStep
set_option autoImplicit false

theorem read {T : Type} (v : Slice T) (i : Usize) (h : i.val < v.val.length) :
    Slice.index_usize v i = ok v.val[i.val] := by
  simp only [Slice.index_usize,Slice.getElem?_Usize_eq]
  rw [List.getElem?_eq_getElem h]

theorem write {T : Type} {N : Usize} (v : Array T N) (i : Usize) (x : T)
    (h : i.val < N.val) : Array.update v i x = ok (v.set i x) := by
  unfold Array.update
  rw [Array.getElem?_Usize_eq,List.getElem?_eq_getElem (by simpa [v.property] using h)]
  rfl

theorem increment (i N : Usize) (h : i.val < N.val) :
    (Usize.wrapping_add i 1#usize).val = i.val+1 := by
  rw [Usize.wrapping_add_val_eq]
  change (i.val+1)%UScalar.size .Usize=i.val+1
  apply Nat.mod_eq_of_lt
  have := N.hSize
  omega

theorem done {T : Type} {N : Usize} (v : Slice T) (out : Array T N) (i : Usize)
    (h : N.val ≤ i.val) :
    PV_CBL_ArrayKernel.array_reference_loop.body v out i = ok (.done out) := by
  have hn : ¬i<N := by change ¬i.val<N.val; omega
  simp only [PV_CBL_ArrayKernel.array_reference_loop.body,hn,if_false]

theorem continuing {T : Type} {N : Usize} (v : Slice T) (out : Array T N) (i : Usize)
    (h : i.val<N.val) (hv : i.val<v.val.length) :
    PV_CBL_ArrayKernel.array_reference_loop.body v out i =
      ok (.cont (out.set i v.val[i.val],Usize.wrapping_add i 1#usize)) := by
  have hn : i<N := h
  simp only [PV_CBL_ArrayKernel.array_reference_loop.body,hn,if_true,read v i hv,
    write out i _ h,lift,bind_tc_ok]
#print axioms read
#print axioms write
#print axioms increment
#print axioms done
#print axioms continuing
end R1Z.PV_CBL_ArrayStep

end

section
-- Exact unchanged source component: R1Z.PV_CBL_ArrayUnfold
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_CBL_ArrayUnfold
set_option autoImplicit false

theorem bind {A B : Type} (step : A → Result (ControlFlow A B)) (a : A) :
    loop step a = (do
      let cf ← step a
      match cf with
      | .cont next => loop step next
      | .done out => .ok out) := by
  rw [loop]
  cases step a <;> rfl

theorem unfold_loop {T : Type} {N : Usize} (v : Slice T) (out : Array T N) (i : Usize) :
    PV_CBL_ArrayKernel.array_reference_loop v out i =
      (do let cf ← PV_CBL_ArrayKernel.array_reference_loop.body v out i
          match cf with
          | .done a => ok a
          | .cont (a,j) => PV_CBL_ArrayKernel.array_reference_loop v a j) := by
  unfold PV_CBL_ArrayKernel.array_reference_loop
  rw [bind]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro cf _
  cases cf with
  | done a => rfl
  | cont next => rcases next with ⟨a,j⟩; rfl
#print axioms bind
#print axioms unfold_loop
end R1Z.PV_CBL_ArrayUnfold

end

section
-- Exact unchanged source component: R1Z.PV_CBL_PadZeroStep
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_CBL_PadZeroStep
set_option autoImplicit false
theorem unfold_loop (out : Array U8 64#usize) (i : Usize) :
    PV_CBL_ShaPadFixed.sha_pad_zero_loop out i =
      (do let cf ← PV_CBL_ShaPadFixed.sha_pad_zero_loop.body out i
          match cf with
          | .done a => ok a
          | .cont (a,j) => PV_CBL_ShaPadFixed.sha_pad_zero_loop a j) := by
  unfold PV_CBL_ShaPadFixed.sha_pad_zero_loop
  rw [PV_CBL_ArrayUnfold.bind]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro cf _
  cases cf with
  | done a => rfl
  | cont next => rcases next with ⟨a,j⟩; rfl
theorem continuing (out : Array U8 64#usize) (i : Usize) (h : i.val<64) :
    PV_CBL_ShaPadFixed.sha_pad_zero_loop.body out i =
      ok (.cont (out.set i 0#u8,Usize.wrapping_add i 1#usize)) := by
  have hn : i<64#usize := h
  simp only [PV_CBL_ShaPadFixed.sha_pad_zero_loop.body,hn,if_true,
    PV_CBL_ArrayStep.write out i 0#u8 h,lift,bind_tc_ok]
theorem done (out : Array U8 64#usize) (i : Usize) (h : (64 : Nat) ≤ i.val) :
    PV_CBL_ShaPadFixed.sha_pad_zero_loop.body out i = ok (.done out) := by
  have hn : ¬ (i < 64#usize) := by change ¬ (i.val < 64); omega
  simp only [PV_CBL_ShaPadFixed.sha_pad_zero_loop.body,hn,if_false]
#print axioms unfold_loop
#print axioms continuing
#print axioms done
end R1Z.PV_CBL_PadZeroStep

end

section
-- Exact unchanged source component: R1Z.PV_CBL_ArrayPrefix
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ArrayPrefix
set_option autoImplicit false

def copied {T : Type} [Inhabited T] {N : Usize} (out : Array T N) (v : Slice T) (k : Nat) : Prop :=
  ∀ j, j<k → j<N.val → out.val[j]! = v.val[j]!

theorem set_get {T : Type} [Inhabited T] {N : Usize} (out : Array T N) (i : Usize)
    (x : T) (j : Nat) (hi : i.val<N.val) :
    (out.set i x).val[j]! = if j=i.val then x else out.val[j]! := by
  simp only [Array.set_val_eq]
  by_cases h : j=i.val
  · subst j
    simp [List.getElem!_eq_getElem?_getD,
      List.getElem?_set_self (show i.val<out.val.length by simpa [out.property] using hi)]
  · simp [List.getElem!_eq_getElem?_getD,h]

theorem advance {T : Type} [Inhabited T] {N : Usize} (out : Array T N) (v : Slice T)
    (i : Usize) (hi : i.val<N.val) (hv : i.val<v.val.length) (h : copied out v i.val) :
    copied (out.set i v.val[i.val]) v (i.val+1) := by
  intro j hj hn
  rw [set_get _ _ _ _ hi]
  split
  · next e => subst j; simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hv]
  · next e => exact h j (by omega) hn

theorem initial {T : Type} [Inhabited T] {N : Usize} (out : Array T N) (v : Slice T) :
    copied out v 0 := by intro j h; omega
#print axioms copied
#print axioms set_get
#print axioms advance
#print axioms initial
end R1Z.PV_CBL_ArrayPrefix

end

section
-- Exact unchanged source component: R1Z.PV_CBL_PadZeroContent
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_CBL_PadZeroContent
set_option autoImplicit false
/-- Each byte below the cursor is retained; every byte from the cursor is zero. -/
theorem loop_content (out : Array U8 64#usize) (i : Usize) :
    ∃ a, PV_CBL_ShaPadFixed.sha_pad_zero_loop out i = ok a ∧
      ∀ (j : Nat), j<64 → a.val[j]! = if j < i.val then out.val[j]! else 0#u8 := by
  generalize he : 64-i.val=fuel
  induction fuel using Nat.strong_induction_on generalizing out i with
  | h fuel ih =>
    rw [PV_CBL_PadZeroStep.unfold_loop]
    by_cases hi : i.val<64
    · rw [PV_CBL_PadZeroStep.continuing out i hi,bind_tc_ok]
      have inc := PV_CBL_ArrayStep.increment i 64#usize hi
      obtain ⟨a,ha,hc⟩ := ih _ (by omega) (out.set i 0#u8)
        (Usize.wrapping_add i 1#usize) rfl
      refine ⟨a,ha,?_⟩
      intro j hj
      rw [hc j hj,inc,PV_CBL_ArrayPrefix.set_get out i 0#u8 j hi]
      by_cases hji : j < i.val
      · rw [if_pos (by omega),if_neg (by omega),if_pos hji]
      · by_cases heq : j=i.val
        · rw [if_pos (by omega),if_pos heq,if_neg hji]
        · rw [if_neg (by omega),if_neg hji]
    · rw [PV_CBL_PadZeroStep.done out i (by omega),bind_tc_ok]
      exact ⟨out,rfl,by intro j hj; rw [if_pos (by omega)]⟩
#print axioms loop_content
end R1Z.PV_CBL_PadZeroContent

end

section
-- Exact unchanged source component: R1Z.PV_CBL_PadDelimitedBytes
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PadDelimitedBytes
set_option autoImplicit false
/-- Exact byte contents, retaining the delimiter and all bytes preceding it. -/
theorem source (out : Array U8 64#usize) (pos : Usize) (hp : pos.val<64) :
    ∃ a, PV_CBL_ShaPadFixed.sha_pad_zero out pos = ok a ∧
      ∀ (j : Nat), j<64 → a.val[j]! =
        if j < pos.val then out.val[j]! else if j=pos.val then 128#u8 else 0#u8 := by
  obtain ⟨a,ha,hc⟩ := PV_CBL_PadZeroContent.loop_content
    (out.set pos 128#u8) (Usize.wrapping_add pos 1#usize)
  refine ⟨a,?_,?_⟩
  · unfold PV_CBL_ShaPadFixed.sha_pad_zero
    rw [PV_CBL_ArrayStep.write out pos 128#u8 hp]
    exact ha
  · intro j hj
    rw [hc j hj,PV_CBL_ArrayStep.increment pos 64#usize hp,
      PV_CBL_ArrayPrefix.set_get out pos 128#u8 j hp]
    by_cases hlt : j < pos.val
    · rw [if_pos (by omega),if_neg (by omega),if_pos hlt]
    · by_cases he : j=pos.val
      · rw [if_pos (by omega),if_pos he,if_neg hlt,if_pos he]
      · rw [if_neg (by omega),if_neg hlt,if_neg he]
#print axioms source
end R1Z.PV_CBL_PadDelimitedBytes

end

section
-- Exact unchanged source component: R1Z.PV_CBL_PaddingModel
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PaddingModel
set_option autoImplicit false
/-- Value-only SHA-256 specialization of digest_pad; source/loan link is separate. -/
def delimited (buffer : List U8) (pos : Nat) : List U8 :=
  buffer.take pos ++ [128#u8] ++ List.replicate (63-pos) 0#u8
def first (buffer : List U8) (pos : Nat) (suffix : List U8) : List U8 :=
  let head := delimited buffer pos
  if pos<56 then head.take 56 ++ suffix else head
def second (pos : Nat) (suffix : List U8) : Option (List U8) :=
  if pos<56 then none else some (List.replicate 56 0#u8 ++ suffix)
def blocks (buffer : List U8) (pos : Nat) (suffix : List U8) : List (List U8) :=
  first buffer pos suffix :: (second pos suffix).toList
/-- The native two-block branch retains the first buffer, not the local second block. -/
def retained (buffer : List U8) (pos : Nat) (suffix : List U8) : List U8 × Nat :=
  (first buffer pos suffix,0)
#print axioms delimited
#print axioms first
#print axioms second
#print axioms blocks
#print axioms retained
end R1Z.PV_CBL_PaddingModel

end

section
-- Exact unchanged source component: R1Z.PV_CBL_PadListFacts
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PadListFacts
set_option autoImplicit false
theorem get_bang {T : Type} [Inhabited T] (l : List T) (i : Nat) (h : i<l.length) :
    l[i]! = l[i] := by
  simp only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem h,Option.getD_some]
theorem ext {T : Type} [Inhabited T] (a b : List T) (hlen : a.length=b.length)
    (h : ∀ i, i<a.length → a[i]! = b[i]!) : a=b := by
  apply List.ext_getElem hlen
  intro i hi hj
  simpa only [get_bang a i hi,get_bang b i hj] using h i hi
#print axioms get_bang
#print axioms ext
end R1Z.PV_CBL_PadListFacts

end

section
-- Exact unchanged source component: R1Z.PV_CBL_PaddingLength
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PaddingLength
open PV_CBL_PaddingModel
set_option autoImplicit false
theorem delimited_length (buffer : List U8) (pos : Nat)
    (hb : buffer.length=64) (hp : pos<64) : (delimited buffer pos).length=64 := by
  simp only [delimited,List.length_append,List.length_take,List.length_singleton,List.length_replicate,hb]
  omega
theorem first_length (buffer suffix : List U8) (pos : Nat)
    (hb : buffer.length=64) (hp : pos<64) (hs : suffix.length=8) :
    (first buffer pos suffix).length=64 := by
  unfold first
  split
  · simp only [List.length_append,List.length_take,delimited_length buffer pos hb hp,hs]
    decide
  · exact delimited_length buffer pos hb hp
theorem second_length (suffix : List U8) (pos : Nat) (hs : suffix.length=8)
    (block : List U8) (h : second pos suffix=some block) : block.length=64 := by
  unfold second at h
  split at h
  · contradiction
  · cases h
    simp [hs]
#print axioms delimited_length
#print axioms first_length
#print axioms second_length
end R1Z.PV_CBL_PaddingLength

end

section
-- Exact unchanged source component: R1Z.PV_CBL_PadModelBytes
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PadModelBytes
set_option autoImplicit false
theorem delimited_byte (buffer : List U8) (pos j : Nat)
    (hb : buffer.length=64) (hp : pos<64) (hj : j<64) :
    (PV_CBL_PaddingModel.delimited buffer pos)[j]! =
      if j < pos then buffer[j]! else if j=pos then 128#u8 else 0#u8 := by
  unfold PV_CBL_PaddingModel.delimited
  rw [List.append_assoc]
  have ht : (buffer.take pos).length=pos := by simp [hb,Nat.min_eq_left (by omega : pos≤64)]
  by_cases hlt : j < pos
  · rw [if_pos hlt]
    simp only [List.getElem!_eq_getElem?_getD]
    rw [List.getElem?_append_left (by simpa [ht] using hlt)]
    simp [List.getElem?_take,show j<pos by exact hlt]
  · rw [if_neg hlt]
    simp only [List.getElem!_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega : (buffer.take pos).length≤j)]
    rw [ht]
    by_cases he : j=pos
    · subst j; simp
    · have hsub : 0<j-pos := by omega
      simp [List.getElem?_cons,show j-pos≠0 by omega,
        List.getElem?_replicate,show j-pos-1<63-pos by omega,he]
#print axioms delimited_byte
end R1Z.PV_CBL_PadModelBytes

end

section
-- Exact unchanged source component: R1Z.PV_CBL_PadDelimitedSource
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PadDelimitedSource
set_option autoImplicit false
theorem source (buffer : Array U8 64#usize) (pos : Usize) (hp : pos.val<64) :
    ∃ a, PV_CBL_ShaPadFixed.sha_pad_zero buffer pos = ok a ∧
      a.val = PV_CBL_PaddingModel.delimited buffer.val pos.val := by
  obtain ⟨a,ha,hc⟩ := PV_CBL_PadDelimitedBytes.source buffer pos hp
  refine ⟨a,ha,PV_CBL_PadListFacts.ext _ _ ?_ ?_⟩
  · rw [a.property,PV_CBL_PaddingLength.delimited_length buffer.val pos.val buffer.property hp]
    rfl
  · intro j hj
    have hj64 : j<64 := by simpa [a.property] using hj
    rw [hc j hj64,PV_CBL_PadModelBytes.delimited_byte buffer.val pos.val j buffer.property hp hj64]
#print axioms source
end R1Z.PV_CBL_PadDelimitedSource

end

section
-- Exact unchanged source component: R1Z.PV_CBL_ArrayReadValue
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ArrayReadValue
set_option autoImplicit false
theorem read {T : Type} [Inhabited T] {N : Usize} (a : Array T N) (i : Usize)
    (h : i.val<N.val) : Array.index_usize a i = ok a.val[i.val]! := by
  have hi : i.val<a.val.length := by simpa only [a.property] using h
  simp only [Array.index_usize,Array.getElem?_Usize_eq,List.getElem?_eq_getElem hi,
    PV_CBL_PadListFacts.get_bang a.val i.val hi]
#print axioms read
end R1Z.PV_CBL_ArrayReadValue

end

section
-- Exact unchanged source component: R1Z.PV_CBL_PadSuffixValue
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PadSuffixValue
set_option autoImplicit false
def value (out : Array U8 64#usize) (suffix : Array U8 8#usize) : Array U8 64#usize :=
  ((((((((out.set 56#usize suffix.val[0]!).set 57#usize suffix.val[1]!).set 58#usize suffix.val[2]!).set 59#usize suffix.val[3]!).set 60#usize suffix.val[4]!).set 61#usize suffix.val[5]!).set 62#usize suffix.val[6]!).set 63#usize suffix.val[7]!)
theorem source (out : Array U8 64#usize) (suffix : Array U8 8#usize) :
    PV_CBL_ShaPadFixed.sha_pad_suffix8 out suffix = ok (value out suffix) := by
  unfold PV_CBL_ShaPadFixed.sha_pad_suffix8
  rw [PV_CBL_ArrayReadValue.read suffix 0#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read suffix 1#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read suffix 2#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read suffix 3#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read suffix 4#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read suffix 5#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read suffix 6#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayReadValue.read suffix 7#usize (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayStep.write _ 56#usize _ (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayStep.write _ 57#usize _ (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayStep.write _ 58#usize _ (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayStep.write _ 59#usize _ (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayStep.write _ 60#usize _ (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayStep.write _ 61#usize _ (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayStep.write _ 62#usize _ (by decide),bind_tc_ok]
  rw [PV_CBL_ArrayStep.write _ 63#usize _ (by decide)]
  rfl
#print axioms value
#print axioms source
end R1Z.PV_CBL_PadSuffixValue

end

section
-- Exact unchanged source component: R1Z.PV_CBL_PadSuffixBytes
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PadSuffixBytes
set_option autoImplicit false
theorem byte (out : Array U8 64#usize) (suffix : Array U8 8#usize) (j : Nat) (hj : j<64) :
    (PV_CBL_PadSuffixValue.value out suffix).val[j]! =
      if j<56 then out.val[j]! else suffix.val[j-56]! := by
  unfold PV_CBL_PadSuffixValue.value
  rw [PV_CBL_ArrayPrefix.set_get _ 63#usize _ j (by decide)]
  rw [PV_CBL_ArrayPrefix.set_get _ 62#usize _ j (by decide)]
  rw [PV_CBL_ArrayPrefix.set_get _ 61#usize _ j (by decide)]
  rw [PV_CBL_ArrayPrefix.set_get _ 60#usize _ j (by decide)]
  rw [PV_CBL_ArrayPrefix.set_get _ 59#usize _ j (by decide)]
  rw [PV_CBL_ArrayPrefix.set_get _ 58#usize _ j (by decide)]
  rw [PV_CBL_ArrayPrefix.set_get _ 57#usize _ j (by decide)]
  rw [PV_CBL_ArrayPrefix.set_get _ 56#usize _ j (by decide)]
  change (if j=63 then suffix.val[7]! else (if j=62 then suffix.val[6]! else (if j=61 then suffix.val[5]! else (if j=60 then suffix.val[4]! else (if j=59 then suffix.val[3]! else (if j=58 then suffix.val[2]! else (if j=57 then suffix.val[1]! else (if j=56 then suffix.val[0]! else out.val[j]!)))))))) = if j<56 then out.val[j]! else suffix.val[j-56]!
  by_cases h : j<56
  · simp only [if_pos h,if_neg (show j≠63 by omega),if_neg (show j≠62 by omega),
      if_neg (show j≠61 by omega),if_neg (show j≠60 by omega),if_neg (show j≠59 by omega),
      if_neg (show j≠58 by omega),if_neg (show j≠57 by omega),if_neg (show j≠56 by omega)]
  · have cases : j=56 ∨ j=57 ∨ j=58 ∨ j=59 ∨ j=60 ∨ j=61 ∨ j=62 ∨ j=63 := by omega
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
#print axioms byte
end R1Z.PV_CBL_PadSuffixBytes

end

section
-- Exact unchanged source component: R1Z.PV_CBL_PadSuffixList
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PadSuffixList
set_option autoImplicit false
theorem append_byte (out suffix : List U8) (ho : out.length=64) (hs : suffix.length=8)
    (j : Nat) (hj : j<64) :
    (out.take 56 ++ suffix)[j]! = if j<56 then out[j]! else suffix[j-56]! := by
  have ht : (out.take 56).length=56 := by simp [ho]
  simp only [List.getElem!_eq_getElem?_getD]
  by_cases h : j<56
  · rw [if_pos h,List.getElem?_append_left (by omega)]
    simp [List.getElem?_take,h]
  · rw [if_neg h,List.getElem?_append_right (by omega),ht]
theorem value (out : Array U8 64#usize) (suffix : Array U8 8#usize) :
    (PV_CBL_PadSuffixValue.value out suffix).val = out.val.take 56 ++ suffix.val := by
  apply PV_CBL_PadListFacts.ext
  · simp [(PV_CBL_PadSuffixValue.value out suffix).property,out.property,suffix.property]
  · intro j hj
    have hj64 : j<64 := by simpa [(PV_CBL_PadSuffixValue.value out suffix).property] using hj
    rw [PV_CBL_PadSuffixBytes.byte out suffix j hj64,
      append_byte out.val suffix.val out.property suffix.property j hj64]
#print axioms append_byte
#print axioms value
end R1Z.PV_CBL_PadSuffixList

end

section
-- Exact unchanged source component: R1Z.PV_CBL_LibraryShapes
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_LibraryShapes
set_option autoImplicit false

/- Field shapes from the byte-pinned generic-array/block-buffer/digest sources.
These are reference carriers, not a callback source-binding certificate. -/
structure Even (T U : Type) where
  parent1 : U
  parent2 : U
  marker : Unit

structure Odd (T U : Type) where
  parent1 : U
  parent2 : U
  data : T

structure GenericArray (T U A : Type) where
  data : A

structure Buffer (A : Type) where
  buffer : A
  pos : U8
  marker : Unit

structure Wrapper (T A : Type) where
  core : T
  buffer : Buffer A

structure CtWrapper (T : Type) where
  inner : T
  marker : Unit

#print axioms Even
#print axioms Odd
#print axioms GenericArray
#print axioms Buffer
#print axioms Wrapper
#print axioms CtWrapper
end R1Z.PV_CBL_LibraryShapes

end

section
-- Exact unchanged source component: R1Z.PV_CBL_BufferReference
namespace R1Z.PV_CBL_BufferReference
open PV_CBL_LibraryShapes
set_option autoImplicit false

/-- The value-only default field shape in block-buffer 0.10.4. Source/default
array initialization and native association are not asserted by this model. -/
def initial {A : Type} (array : A) : Buffer A := ⟨array,0#u8,()⟩

def data {T : Type} (flatten : T→List Aeneas.Std.U8) (v : Buffer T) : List Aeneas.Std.U8 :=
  (flatten v.buffer).take v.pos.val

theorem initial_pos {A : Type} (a : A) : (initial a).pos.val=0 := rfl

theorem initial_data {T : Type} (flatten : T→List Aeneas.Std.U8) (a : T) :
    data flatten (initial a)=[] := by simp [data,initial]

theorem data_length {T : Type} (flatten : T→List Aeneas.Std.U8) (v : Buffer T)
    (h : v.pos.val≤(flatten v.buffer).length) : (data flatten v).length=v.pos.val := by
  simp only [data,List.length_take,Nat.min_eq_left h]

#print axioms initial
#print axioms data
#print axioms initial_pos
#print axioms initial_data
#print axioms data_length
end R1Z.PV_CBL_BufferReference

end

section
-- Exact unchanged source component: R1Z.PV_CBL_BufferInvariants
namespace R1Z.PV_CBL_BufferInvariants
open PV_CBL_LibraryShapes
set_option autoImplicit false

def eager {A : Type} (size : Nat) (v : Buffer A) : Prop := v.pos.val<size

def lazy {A : Type} (size : Nat) (v : Buffer A) : Prop := v.pos.val≤size

theorem eager_implies_lazy {A : Type} (size : Nat) (v : Buffer A) (h : eager size v) :
    lazy size v := Nat.le_of_lt h

theorem initial_eager {A : Type} (size : Nat) (a : A) (h : 0<size) :
    eager size (PV_CBL_BufferReference.initial a) := h

theorem initial_lazy {A : Type} (size : Nat) (a : A) :
    lazy size (PV_CBL_BufferReference.initial a) := Nat.zero_le size

#print axioms eager
#print axioms lazy
#print axioms eager_implies_lazy
#print axioms initial_eager
#print axioms initial_lazy
end R1Z.PV_CBL_BufferInvariants

end

section
-- Exact unchanged source component: R1Z.PV_CBL_PaddingBranch
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PaddingBranch
set_option autoImplicit false
theorem branch (pos : Nat) (h : pos<64) : 64-pos-1<8 ↔ 56≤pos := by omega
theorem one_block (pos : Nat) (h : pos<56) : ¬64-pos-1<8 := by omega
theorem two_block (pos : Nat) (h : 56≤pos) (h64 : pos<64) : 64-pos-1<8 := by omega
theorem delimiter_bounds (pos : Nat) (h : pos<64) : pos+1≤64 := by omega
theorem suffix_start : 64-8=56 := rfl
#print axioms branch
#print axioms one_block
#print axioms two_block
#print axioms delimiter_bounds
#print axioms suffix_start
end R1Z.PV_CBL_PaddingBranch

end

section
-- Exact unchanged source component: R1Z.PV_CBL_PadBranchValue
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PadBranchValue
set_option autoImplicit false
theorem remaining (pos : Usize) (hp : pos.val<64) :
    (Usize.wrapping_sub (Usize.wrapping_sub 64#usize pos) 1#usize).val = 64-pos.val-1 := by
  rw [Usize.wrapping_sub_val_eq]
  have h1 : (Usize.wrapping_sub 64#usize pos).val = 64-pos.val := by
    rw [Usize.wrapping_sub_val_eq]
    change (64+(UScalar.size .Usize-pos.val))%UScalar.size .Usize=64-pos.val
    have hmax := (64#usize).hSize
    change 64 < UScalar.size .Usize at hmax
    have he : 64+(UScalar.size .Usize-pos.val)=UScalar.size .Usize+(64-pos.val) := by omega
    rw [he,Nat.add_mod,Nat.mod_self,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt (by omega)]
  rw [h1]
  change (64-pos.val+(UScalar.size .Usize-1))%UScalar.size .Usize=64-pos.val-1
  have hmax := (64#usize).hSize
  change 64 < UScalar.size .Usize at hmax
  have he : 64-pos.val+(UScalar.size .Usize-1)=UScalar.size .Usize+(64-pos.val-1) := by omega
  rw [he,Nat.add_mod,Nat.mod_self,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt (by omega)]
theorem branch (pos : Usize) (hp : pos.val<64) :
    (Usize.wrapping_sub (Usize.wrapping_sub 64#usize pos) 1#usize < 8#usize) ↔
      56≤pos.val := by
  change (Usize.wrapping_sub (Usize.wrapping_sub 64#usize pos) 1#usize).val < 8 ↔ _
  rw [remaining pos hp]
  omega
#print axioms remaining
#print axioms branch
end R1Z.PV_CBL_PadBranchValue

end

section
-- Exact unchanged source component: R1Z.PV_CBL_PadOneSource
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PadOneSource
set_option autoImplicit false
theorem source (buffer : Array U8 64#usize) (pos : Usize) (suffix : Array U8 8#usize)
    (hp : pos.val<56) :
    ∃ first, PV_CBL_ShaPadFixed.sha_pad_owned_split8 buffer pos suffix =
      ok (first,none,first,0#usize) ∧
      first.val = PV_CBL_PaddingModel.first buffer.val pos.val suffix.val := by
  obtain ⟨head,hh,hv⟩ := PV_CBL_PadDelimitedSource.source buffer pos (by omega)
  have hn : ¬(Usize.wrapping_sub (Usize.wrapping_sub 64#usize pos) 1#usize < 8#usize) := by
    rw [PV_CBL_PadBranchValue.branch pos (by omega)]; omega
  refine ⟨PV_CBL_PadSuffixValue.value head suffix,?_,?_⟩
  · unfold PV_CBL_ShaPadFixed.sha_pad_owned_split8
    rw [hh]
    simp only [lift,bind_tc_ok,if_neg hn,PV_CBL_PadSuffixValue.source]
  · rw [PV_CBL_PadSuffixList.value,hv]
    simp only [PV_CBL_PaddingModel.first,if_pos hp]
#print axioms source
end R1Z.PV_CBL_PadOneSource

end

section
-- Exact unchanged source component: R1Z.PV_CBL_PadTwoSource
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PadTwoSource
set_option autoImplicit false
theorem source (buffer : Array U8 64#usize) (pos : Usize) (suffix : Array U8 8#usize)
    (hp : pos.val<64) (h56 : 56≤pos.val) :
    ∃ first second, PV_CBL_ShaPadFixed.sha_pad_owned_split8 buffer pos suffix =
      ok (first,some second,first,0#usize) ∧
      first.val = PV_CBL_PaddingModel.first buffer.val pos.val suffix.val ∧
      some second.val = PV_CBL_PaddingModel.second pos.val suffix.val := by
  obtain ⟨head,hh,hv⟩ := PV_CBL_PadDelimitedSource.source buffer pos hp
  have hc := (PV_CBL_PadBranchValue.branch pos hp).mpr h56
  refine ⟨head,PV_CBL_PadSuffixValue.value (Array.repeat 64#usize 0#u8) suffix,?_,?_,?_⟩
  · unfold PV_CBL_ShaPadFixed.sha_pad_owned_split8
    rw [hh]
    simp only [lift,bind_tc_ok,if_pos hc,PV_CBL_PadSuffixValue.source]
  · simp only [PV_CBL_PaddingModel.first,if_neg (show ¬pos.val<56 by omega)]
    exact hv
  · rw [PV_CBL_PadSuffixList.value]
    simp [PV_CBL_PaddingModel.second,show ¬pos.val<56 by omega,Array.repeat]
#print axioms source
end R1Z.PV_CBL_PadTwoSource

end

section
-- Exact unchanged source component: R1Z.PV_CBL_PadContentSource
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PadContentSource
set_option autoImplicit false
/-- Full content, retained-buffer and reset-position law of the extracted owned
reference. The native loan/callback/destructor link is a separate obligation. -/
theorem source (buffer : Array U8 64#usize) (pos : Usize) (suffix : Array U8 8#usize)
    (hp : pos.val<64) :
    ∃ first second, PV_CBL_ShaPadFixed.sha_pad_owned_split8 buffer pos suffix =
      ok (first,second,first,0#usize) ∧
      first.val = PV_CBL_PaddingModel.first buffer.val pos.val suffix.val ∧
      second.map (fun a => a.val) = PV_CBL_PaddingModel.second pos.val suffix.val := by
  by_cases h : pos.val<56
  · obtain ⟨first,hf,hv⟩ := PV_CBL_PadOneSource.source buffer pos suffix h
    exact ⟨first,none,hf,hv,by simp [PV_CBL_PaddingModel.second,h]⟩
  · obtain ⟨first,second,hf,hv,hs⟩ := PV_CBL_PadTwoSource.source buffer pos suffix hp (by omega)
    exact ⟨first,some second,hf,hv,hs⟩
#print axioms source
end R1Z.PV_CBL_PadContentSource

end

section
-- Exact unchanged source component: R1Z.PV_CBL_PaddingCount
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PaddingCount
open PV_CBL_PaddingModel
set_option autoImplicit false
theorem one (buffer suffix : List U8) (pos : Nat) (h : pos<56) :
    blocks buffer pos suffix = [first buffer pos suffix] := by simp [blocks,second,h]
theorem two (buffer suffix : List U8) (pos : Nat) (h : 56≤pos) :
    blocks buffer pos suffix = [first buffer pos suffix,List.replicate 56 0#u8 ++ suffix] := by
  simp [blocks,second,show ¬pos<56 by omega]
theorem count (buffer suffix : List U8) (pos : Nat) :
    (blocks buffer pos suffix).length = if pos<56 then 1 else 2 := by
  by_cases h : pos<56
  · simp [one buffer suffix pos h,h]
  · simp [two buffer suffix pos (by omega),h]
#print axioms one
#print axioms two
#print axioms count
end R1Z.PV_CBL_PaddingCount

end

section
-- Exact unchanged source component: R1Z.PV_DL_CompressionTrace
open Aeneas Aeneas.Std Result
namespace R1Z.PV_DL_CompressionTrace
set_option autoImplicit false

/-- A compression callback is a parameter, including its Result behavior.
No SHA-NI semantics, backend equality, or totality is assumed. -/
def run {S B : Type} (compress : S → B → Result S) : List B → S → Result S
  | [],state => ok state
  | block::tail,state => do
    let next ← compress state block
    run compress tail next

theorem empty {S B : Type} (compress : S → B → Result S) (state : S) :
    run compress [] state=ok state := rfl

theorem append {S B : Type} (compress : S → B → Result S)
    (a b : List B) (state : S) :
    run compress (a++b) state=(do let next ← run compress a state;run compress b next) := by
  induction a generalizing state with
  | nil => simp only [List.nil_append,run,bind_tc_ok]
  | cons block tail ih =>
    simp only [List.cons_append,run,bind_assoc_eq]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro next hnext
    exact ih next

theorem event_transport {S B : Type} (native reference : List B)
    (events : native=reference) (state : S) :
    ∀ compress : S → B → Result S,
      run compress native state=run compress reference state := by
  intro compress
  rw [events]

/-- Both backend instances follow from event transport independently. -/
theorem backend_instances {S B : Type} (native reference : List B)
    (events : native=reference) (state : S)
    (soft shani : S → B → Result S) :
    run soft native state=run soft reference state ∧
    run shani native state=run shani reference state :=
  ⟨event_transport native reference events state soft,
   event_transport native reference events state shani⟩

#print axioms run
#print axioms empty
#print axioms append
#print axioms event_transport
#print axioms backend_instances
end R1Z.PV_DL_CompressionTrace

end

section
-- Exact unchanged source component: R1Z.PV_DL_FinalizeParam
open Aeneas Aeneas.Std Result
namespace R1Z.PV_DL_FinalizeParam
set_option autoImplicit false

def reference {S : Type} (compress : S → List U8 → Result S) (state : S)
    (buffer : Array U8 64#usize) (pos : Usize) (suffix : Array U8 8#usize) :
    Result (S × List U8 × Nat) := do
  let (first,second,retained,pos) ← PV_CBL_ShaPadFixed.sha_pad_owned_split8 buffer pos suffix
  let state ← PV_DL_CompressionTrace.run compress
    (first.val::(second.map (fun (a : Array U8 64#usize) => a.val)).toList) state
  ok (state,retained.val,pos.val)

def model {S : Type} (compress : S → List U8 → Result S) (state : S)
    (buffer : List U8) (pos : Nat) (suffix : List U8) : Result (S × List U8 × Nat) := do
  let state ← PV_DL_CompressionTrace.run compress
    (PV_CBL_PaddingModel.blocks buffer pos suffix) state
  ok (state,PV_CBL_PaddingModel.first buffer pos suffix,0)

/-- Reuse the complete extracted padding content/restoration law. Compression
is an arbitrary Result-valued parameter, preserving failures and divergence. -/
theorem source {S : Type} (compress : S → List U8 → Result S) (state : S)
    (buffer : Array U8 64#usize) (pos : Usize) (suffix : Array U8 8#usize)
    (hp : pos.val<64) :
    reference compress state buffer pos suffix=
      model compress state buffer.val pos.val suffix.val := by
  obtain ⟨first,second,hpad,hfirst,hsecond⟩ :=
    PV_CBL_PadContentSource.source buffer pos suffix hp
  unfold reference
  rw [hpad]
  change (do
    let next ← PV_DL_CompressionTrace.run compress
      (first.val::(second.map (fun (a : Array U8 64#usize) => a.val)).toList) state
    ok (next,first.val,0)) = _
  rw [hfirst,hsecond]
  rfl

theorem callback_count (buffer suffix : List U8) (pos : Nat) :
    (PV_CBL_PaddingModel.blocks buffer pos suffix).length=if pos<56 then 1 else 2 :=
  PV_CBL_PaddingCount.count buffer suffix pos

#print axioms reference
#print axioms model
#print axioms source
#print axioms callback_count
end R1Z.PV_DL_FinalizeParam

end

section
-- Exact unchanged source component: R1Z.PV_CBL_ShaCore
-- Exact two-field carrier retained from op208-opt-generated/Types.lean.
open Aeneas Aeneas.Std Result
namespace PV_CBL_ShaCore
structure Core where
  state : Array U32 8#usize
  block_len : U64
#print axioms Core
end PV_CBL_ShaCore

end

section
-- Exact unchanged source component: R1Z.PV_CBL_ShaTypes
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ShaTypes
open ProverRwFull
set_option autoImplicit false
@[reducible] def selectedTypes (base : ExternalTypes) : ExternalTypes :=
  { base with op10 := PV_CBL_ShaCore.Core }
abbrev Blocks (base : ExternalTypes) : Type :=
  letI : ExternalTypes := base
  Slice (generic_array.GenericArray Std.U8
        (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt
        (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt typenum.uint.UTerm
        typenum.bit.B1) typenum.bit.B0) typenum.bit.B0) typenum.bit.B0)
        typenum.bit.B0) typenum.bit.B0) typenum.bit.B0)
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplOdd Std.U8 (Array Std.U8 0#usize)))))))))
theorem core_carrier (base : ExternalTypes) :
    @sha2.core_api.Sha256VarCore (selectedTypes base) = PV_CBL_ShaCore.Core := rfl

theorem blocks_carrier (base : ExternalTypes) :
    Blocks (selectedTypes base) = Blocks base := rfl
#print axioms core_carrier
#print axioms blocks_carrier
end R1Z.PV_CBL_ShaTypes

end

section
-- Exact unchanged source component: R1Z.PV_CBL_Op208Extracted
-- Body retained from op208-opt-generated/Funs.lean. The still-opaque
-- compress256 symbol is an explicit parameter, not a new axiom or source law.
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_Op208Extracted
open ProverRwFull
set_option autoImplicit false
abbrev Compression (base : ExternalTypes) :=
  Array U32 8#usize → PV_CBL_ShaTypes.Blocks base → Result (Array U32 8#usize)

def update_blocks (base : ExternalTypes) (compress : Compression base)
    (self : PV_CBL_ShaCore.Core) (blocks : PV_CBL_ShaTypes.Blocks base) :
    Result PV_CBL_ShaCore.Core := do
  let i := Slice.len blocks
  let i1 ← lift (UScalar.cast .U64 i)
  let i2 ← lift (U64.wrapping_add self.block_len i1)
  let a ← compress self.state blocks
  ok { state := a, block_len := i2 }
#print axioms update_blocks
end R1Z.PV_CBL_Op208Extracted

end

section
-- Exact unchanged source component: R1Z.PV_CBL_ShaCount
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ShaCount
set_option autoImplicit false

theorem cast_count (n : Usize) : (UScalar.cast .U64 n).val = n.val := by
  rw [UScalar.cast_val_eq]
  refine Nat.mod_eq_of_lt (lt_of_lt_of_le n.hBounds ?_)
  simp only [UScalarTy.U64_numBits_eq, UScalarTy.Usize_numBits_eq]
  exact Nat.pow_le_pow_right (by omega) (by cases System.Platform.numBits_eq <;> simp_all)

theorem wrapping_count (old : U64) (n : Usize) :
    (U64.wrapping_add old (UScalar.cast .U64 n)).val =
      (old.val+n.val) % 2^64 := by
  rw [U64.wrapping_add_val_eq,cast_count]
  simp only [UScalar.size, UScalarTy.numBits]

theorem zero_count (old : U64) :
    U64.wrapping_add old (UScalar.cast .U64 0#usize) = old := by
  apply UScalar.eq_of_val_eq
  rw [wrapping_count]
  change (old.val+0) % 2^64 = old.val
  simp only [Nat.add_zero]
  exact Nat.mod_eq_of_lt (by simpa only [UScalar.size, UScalarTy.numBits] using old.hSize)

#print axioms cast_count
#print axioms wrapping_count
#print axioms zero_count
end R1Z.PV_CBL_ShaCount

end

section
-- Exact unchanged source component: R1Z.PV_CBL_ShaBitLength
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ShaBitLength
set_option autoImplicit false

/-- Arithmetic subexpression of sha2 0.10.9 core_api.rs finalization in the
frozen release wrapping profile; padding/compression binding is still open. -/
def bitLength (pos : Usize) (blocks : U64) : U64 :=
  U64.wrapping_mul 8#u64
    (U64.wrapping_add (UScalar.cast .U64 pos) (U64.wrapping_mul 64#u64 blocks))

theorem value (pos : Usize) (blocks : U64) :
    (bitLength pos blocks).val = (8*(pos.val+64*blocks.val))%2^64 := by
  simp only [bitLength,U64.wrapping_mul_val_eq,U64.wrapping_add_val_eq,
    PV_CBL_ShaCount.cast_count,UScalar.size,UScalarTy.numBits]
  change (8*((pos.val+(64*blocks.val)%2^64)%2^64))%2^64 = _
  simp only [Nat.mul_mod,Nat.add_mod,Nat.mod_mod]

#print axioms bitLength
#print axioms value
end R1Z.PV_CBL_ShaBitLength

end

section
-- Exact unchanged source component: R1Z.PV_DL_LengthEncoding
open Aeneas Aeneas.Std Result
namespace R1Z.PV_DL_LengthEncoding
set_option autoImplicit false

/-- Explicit big-endian suffix. Only eight byte casts are constructed. -/
def suffix (bits : U64) : Array U8 8#usize :=
  Array.make 8#usize [UScalar.cast .U8 (U64.wrapping_shr bits 56#u32),
    UScalar.cast .U8 (U64.wrapping_shr bits 48#u32),
    UScalar.cast .U8 (U64.wrapping_shr bits 40#u32),
    UScalar.cast .U8 (U64.wrapping_shr bits 32#u32),
    UScalar.cast .U8 (U64.wrapping_shr bits 24#u32),
    UScalar.cast .U8 (U64.wrapping_shr bits 16#u32),
    UScalar.cast .U8 (U64.wrapping_shr bits 8#u32),UScalar.cast .U8 bits]

theorem suffix_length (bits : U64) : (suffix bits).val.length=8 :=
  (suffix bits).property

theorem length_value (pos : Usize) (blocks : U64) :
    (PV_CBL_ShaBitLength.bitLength pos blocks).val=(8*(pos.val+64*blocks.val))%2^64 :=
  PV_CBL_ShaBitLength.value pos blocks

def finalize {S : Type} (compress : S → List U8 → Result S) (state : S)
    (blocks : U64) (buffer : Array U8 64#usize) (pos : Usize) : Result (S × List U8 × Nat) :=
  PV_DL_FinalizeParam.reference compress state buffer pos
    (suffix (PV_CBL_ShaBitLength.bitLength pos blocks))

theorem source {S : Type} (compress : S → List U8 → Result S) (state : S)
    (blocks : U64) (buffer : Array U8 64#usize) (pos : Usize) (hp : pos.val<64) :
    finalize compress state blocks buffer pos=
      PV_DL_FinalizeParam.model compress state buffer.val pos.val
        (suffix (PV_CBL_ShaBitLength.bitLength pos blocks)).val :=
  PV_DL_FinalizeParam.source compress state buffer pos _ hp

#print axioms suffix
#print axioms suffix_length
#print axioms length_value
#print axioms finalize
#print axioms source
end R1Z.PV_DL_LengthEncoding

end

section
-- Exact unchanged source component: R1Z.PV_CBL_ShaBytes
-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
-- [pv_cblib_source]: function definitions
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048

namespace PV_CBL_ShaBytes

/-- [pv_cblib_source::sha_load_be4]:
    Source: 'lib.rs', lines 462:0-464:1
    Visibility: public -/
def sha_load_be4 (b : Array Std.U8 4#usize) : Result Std.U32 := do
  let i ← Array.index_usize b 0#usize
  let i1 ← lift (UScalar.cast .U32 i)
  let i2 ← lift (Std.U32.wrapping_shl i1 24#u32)
  let i3 ← Array.index_usize b 1#usize
  let i4 ← lift (UScalar.cast .U32 i3)
  let i5 ← lift (Std.U32.wrapping_shl i4 16#u32)
  let i6 ← lift (i2 ||| i5)
  let i7 ← Array.index_usize b 2#usize
  let i8 ← lift (UScalar.cast .U32 i7)
  let i9 ← lift (Std.U32.wrapping_shl i8 8#u32)
  let i10 ← lift (i6 ||| i9)
  let i11 ← Array.index_usize b 3#usize
  let i12 ← lift (UScalar.cast .U32 i11)
  ok (i10 ||| i12)

/-- [pv_cblib_source::sha_store_be4]:
    Source: 'lib.rs', lines 465:0-467:1
    Visibility: public -/
def sha_store_be4 (w : Std.U32) : Result (Array Std.U8 4#usize) := do
  let i ← lift (Std.U32.wrapping_shr w 24#u32)
  let i1 ← lift (UScalar.cast .U8 i)
  let i2 ← lift (Std.U32.wrapping_shr w 16#u32)
  let i3 ← lift (UScalar.cast .U8 i2)
  let i4 ← lift (Std.U32.wrapping_shr w 8#u32)
  let i5 ← lift (UScalar.cast .U8 i4)
  let i6 ← lift (UScalar.cast .U8 w)
  ok (Array.make 4#usize [ i1, i3, i5, i6 ])

/-- [pv_cblib_source::sha_load_lane0]:
    Source: 'lib.rs', lines 468:0-468:77
    Visibility: public -/
def sha_load_lane0 (b : Array Std.U8 64#usize) : Result Std.U32 := do
  let i ← Array.index_usize b 0#usize
  let i1 ← Array.index_usize b 1#usize
  let i2 ← Array.index_usize b 2#usize
  let i3 ← Array.index_usize b 3#usize
  sha_load_be4 (Array.make 4#usize [ i, i1, i2, i3 ])

/-- [pv_cblib_source::sha_load_lane1]:
    Source: 'lib.rs', lines 469:0-469:77
    Visibility: public -/
def sha_load_lane1 (b : Array Std.U8 64#usize) : Result Std.U32 := do
  let i ← Array.index_usize b 4#usize
  let i1 ← Array.index_usize b 5#usize
  let i2 ← Array.index_usize b 6#usize
  let i3 ← Array.index_usize b 7#usize
  sha_load_be4 (Array.make 4#usize [ i, i1, i2, i3 ])

/-- [pv_cblib_source::sha_load_lane2]:
    Source: 'lib.rs', lines 470:0-470:79
    Visibility: public -/
def sha_load_lane2 (b : Array Std.U8 64#usize) : Result Std.U32 := do
  let i ← Array.index_usize b 8#usize
  let i1 ← Array.index_usize b 9#usize
  let i2 ← Array.index_usize b 10#usize
  let i3 ← Array.index_usize b 11#usize
  sha_load_be4 (Array.make 4#usize [ i, i1, i2, i3 ])

/-- [pv_cblib_source::sha_load_lane3]:
    Source: 'lib.rs', lines 471:0-471:81
    Visibility: public -/
def sha_load_lane3 (b : Array Std.U8 64#usize) : Result Std.U32 := do
  let i ← Array.index_usize b 12#usize
  let i1 ← Array.index_usize b 13#usize
  let i2 ← Array.index_usize b 14#usize
  let i3 ← Array.index_usize b 15#usize
  sha_load_be4 (Array.make 4#usize [ i, i1, i2, i3 ])

/-- [pv_cblib_source::sha_load_lane4]:
    Source: 'lib.rs', lines 472:0-472:81
    Visibility: public -/
def sha_load_lane4 (b : Array Std.U8 64#usize) : Result Std.U32 := do
  let i ← Array.index_usize b 16#usize
  let i1 ← Array.index_usize b 17#usize
  let i2 ← Array.index_usize b 18#usize
  let i3 ← Array.index_usize b 19#usize
  sha_load_be4 (Array.make 4#usize [ i, i1, i2, i3 ])

/-- [pv_cblib_source::sha_load_lane5]:
    Source: 'lib.rs', lines 473:0-473:81
    Visibility: public -/
def sha_load_lane5 (b : Array Std.U8 64#usize) : Result Std.U32 := do
  let i ← Array.index_usize b 20#usize
  let i1 ← Array.index_usize b 21#usize
  let i2 ← Array.index_usize b 22#usize
  let i3 ← Array.index_usize b 23#usize
  sha_load_be4 (Array.make 4#usize [ i, i1, i2, i3 ])

/-- [pv_cblib_source::sha_load_lane6]:
    Source: 'lib.rs', lines 474:0-474:81
    Visibility: public -/
def sha_load_lane6 (b : Array Std.U8 64#usize) : Result Std.U32 := do
  let i ← Array.index_usize b 24#usize
  let i1 ← Array.index_usize b 25#usize
  let i2 ← Array.index_usize b 26#usize
  let i3 ← Array.index_usize b 27#usize
  sha_load_be4 (Array.make 4#usize [ i, i1, i2, i3 ])

/-- [pv_cblib_source::sha_load_lane7]:
    Source: 'lib.rs', lines 475:0-475:81
    Visibility: public -/
def sha_load_lane7 (b : Array Std.U8 64#usize) : Result Std.U32 := do
  let i ← Array.index_usize b 28#usize
  let i1 ← Array.index_usize b 29#usize
  let i2 ← Array.index_usize b 30#usize
  let i3 ← Array.index_usize b 31#usize
  sha_load_be4 (Array.make 4#usize [ i, i1, i2, i3 ])

/-- [pv_cblib_source::sha_load_lane8]:
    Source: 'lib.rs', lines 476:0-476:81
    Visibility: public -/
def sha_load_lane8 (b : Array Std.U8 64#usize) : Result Std.U32 := do
  let i ← Array.index_usize b 32#usize
  let i1 ← Array.index_usize b 33#usize
  let i2 ← Array.index_usize b 34#usize
  let i3 ← Array.index_usize b 35#usize
  sha_load_be4 (Array.make 4#usize [ i, i1, i2, i3 ])

/-- [pv_cblib_source::sha_load_lane9]:
    Source: 'lib.rs', lines 477:0-477:81
    Visibility: public -/
def sha_load_lane9 (b : Array Std.U8 64#usize) : Result Std.U32 := do
  let i ← Array.index_usize b 36#usize
  let i1 ← Array.index_usize b 37#usize
  let i2 ← Array.index_usize b 38#usize
  let i3 ← Array.index_usize b 39#usize
  sha_load_be4 (Array.make 4#usize [ i, i1, i2, i3 ])

/-- [pv_cblib_source::sha_load_lane10]:
    Source: 'lib.rs', lines 478:0-478:82
    Visibility: public -/
def sha_load_lane10 (b : Array Std.U8 64#usize) : Result Std.U32 := do
  let i ← Array.index_usize b 40#usize
  let i1 ← Array.index_usize b 41#usize
  let i2 ← Array.index_usize b 42#usize
  let i3 ← Array.index_usize b 43#usize
  sha_load_be4 (Array.make 4#usize [ i, i1, i2, i3 ])

/-- [pv_cblib_source::sha_load_lane11]:
    Source: 'lib.rs', lines 479:0-479:82
    Visibility: public -/
def sha_load_lane11 (b : Array Std.U8 64#usize) : Result Std.U32 := do
  let i ← Array.index_usize b 44#usize
  let i1 ← Array.index_usize b 45#usize
  let i2 ← Array.index_usize b 46#usize
  let i3 ← Array.index_usize b 47#usize
  sha_load_be4 (Array.make 4#usize [ i, i1, i2, i3 ])

/-- [pv_cblib_source::sha_load_lane12]:
    Source: 'lib.rs', lines 480:0-480:82
    Visibility: public -/
def sha_load_lane12 (b : Array Std.U8 64#usize) : Result Std.U32 := do
  let i ← Array.index_usize b 48#usize
  let i1 ← Array.index_usize b 49#usize
  let i2 ← Array.index_usize b 50#usize
  let i3 ← Array.index_usize b 51#usize
  sha_load_be4 (Array.make 4#usize [ i, i1, i2, i3 ])

/-- [pv_cblib_source::sha_load_lane13]:
    Source: 'lib.rs', lines 481:0-481:82
    Visibility: public -/
def sha_load_lane13 (b : Array Std.U8 64#usize) : Result Std.U32 := do
  let i ← Array.index_usize b 52#usize
  let i1 ← Array.index_usize b 53#usize
  let i2 ← Array.index_usize b 54#usize
  let i3 ← Array.index_usize b 55#usize
  sha_load_be4 (Array.make 4#usize [ i, i1, i2, i3 ])

/-- [pv_cblib_source::sha_load_lane14]:
    Source: 'lib.rs', lines 482:0-482:82
    Visibility: public -/
def sha_load_lane14 (b : Array Std.U8 64#usize) : Result Std.U32 := do
  let i ← Array.index_usize b 56#usize
  let i1 ← Array.index_usize b 57#usize
  let i2 ← Array.index_usize b 58#usize
  let i3 ← Array.index_usize b 59#usize
  sha_load_be4 (Array.make 4#usize [ i, i1, i2, i3 ])

/-- [pv_cblib_source::sha_load_lane15]:
    Source: 'lib.rs', lines 483:0-483:82
    Visibility: public -/
def sha_load_lane15 (b : Array Std.U8 64#usize) : Result Std.U32 := do
  let i ← Array.index_usize b 60#usize
  let i1 ← Array.index_usize b 61#usize
  let i2 ← Array.index_usize b 62#usize
  let i3 ← Array.index_usize b 63#usize
  sha_load_be4 (Array.make 4#usize [ i, i1, i2, i3 ])

/-- [pv_cblib_source::sha_load64]:
    Source: 'lib.rs', lines 484:0-484:338
    Visibility: public -/
def sha_load64
  (b : Array Std.U8 64#usize) : Result (Array Std.U32 16#usize) := do
  let i ← sha_load_lane0 b
  let i1 ← sha_load_lane1 b
  let i2 ← sha_load_lane2 b
  let i3 ← sha_load_lane3 b
  let i4 ← sha_load_lane4 b
  let i5 ← sha_load_lane5 b
  let i6 ← sha_load_lane6 b
  let i7 ← sha_load_lane7 b
  let i8 ← sha_load_lane8 b
  let i9 ← sha_load_lane9 b
  let i10 ← sha_load_lane10 b
  let i11 ← sha_load_lane11 b
  let i12 ← sha_load_lane12 b
  let i13 ← sha_load_lane13 b
  let i14 ← sha_load_lane14 b
  let i15 ← sha_load_lane15 b
  ok
    (Array.make 16#usize [
      i, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15
      ])

/-- [pv_cblib_source::sha_byte_codec_root]:
    Source: 'lib.rs', lines 485:0-485:97
    Visibility: public -/
def sha_byte_codec_root
  (b : Array Std.U8 64#usize) (w : Std.U32) :
  Result ((Array Std.U32 16#usize) × (Array Std.U8 4#usize))
  := do
  let a ← sha_load64 b
  let a1 ← sha_store_be4 w
  ok (a, a1)

#print axioms sha_load_be4
#print axioms sha_store_be4
#print axioms sha_load_lane0
#print axioms sha_load_lane1
#print axioms sha_load_lane2
#print axioms sha_load_lane3
#print axioms sha_load_lane4
#print axioms sha_load_lane5
#print axioms sha_load_lane6
#print axioms sha_load_lane7
#print axioms sha_load_lane8
#print axioms sha_load_lane9
#print axioms sha_load_lane10
#print axioms sha_load_lane11
#print axioms sha_load_lane12
#print axioms sha_load_lane13
#print axioms sha_load_lane14
#print axioms sha_load_lane15
#print axioms sha_load64
#print axioms sha_byte_codec_root
end PV_CBL_ShaBytes

end

section
-- Exact unchanged source component: R1Z.PV_CBL_ByteCodecValue
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ByteCodecValue
set_option autoImplicit false
def load (a b c d : U8) : U32 :=
  ((U32.wrapping_shl (UScalar.cast .U32 a) 24#u32 |||
    U32.wrapping_shl (UScalar.cast .U32 b) 16#u32) |||
    U32.wrapping_shl (UScalar.cast .U32 c) 8#u32) ||| UScalar.cast .U32 d
def store (w : U32) : Array U8 4#usize :=
  Array.make 4#usize [UScalar.cast .U8 (U32.wrapping_shr w 24#u32),
    UScalar.cast .U8 (U32.wrapping_shr w 16#u32),
    UScalar.cast .U8 (U32.wrapping_shr w 8#u32),UScalar.cast .U8 w]
theorem store_source (w : U32) : PV_CBL_ShaBytes.sha_store_be4 w = ok (store w) := rfl
#print axioms load
#print axioms store
#print axioms store_source
end R1Z.PV_CBL_ByteCodecValue

end

section
-- Exact unchanged source component: R1Z.PV_DL_ShaSerialize
open Aeneas Aeneas.Std Result
namespace R1Z.PV_DL_ShaSerialize
set_option autoImplicit false

def bytes (words : List U32) : List U8 :=
  words.flatMap (fun w => (PV_CBL_ByteCodecValue.store w).val)

def reference : List U32 → Result (List U8)
  | [] => ok []
  | w::tail => do
    let four ← PV_CBL_ShaBytes.sha_store_be4 w
    let rest ← reference tail
    ok (four.val++rest)

theorem source (words : List U32) : reference words=ok (bytes words) := by
  induction words with
  | nil => rfl
  | cons w tail ih =>
    simp only [reference,PV_CBL_ByteCodecValue.store_source,ih,bind_tc_ok,
      bytes,List.flatMap_cons]

theorem length (words : List U32) : (bytes words).length=4*words.length := by
  induction words with
  | nil => rfl
  | cons w tail ih =>
    change ((PV_CBL_ByteCodecValue.store w).val++bytes tail).length=4*(tail.length+1)
    rw [List.length_append,(PV_CBL_ByteCodecValue.store w).property,ih]
    change 4+4*tail.length=4*(tail.length+1)
    omega

def array (state : Array U32 8#usize) : Array U8 32#usize :=
  ⟨bytes state.val,by rw [length,state.property];rfl⟩

theorem total (state : Array U32 8#usize) :
    reference state.val=ok (array state).val := source state.val

#print axioms bytes
#print axioms reference
#print axioms source
#print axioms length
#print axioms array
#print axioms total
end R1Z.PV_DL_ShaSerialize

end

section
-- Exact unchanged source component: R1Z.PV_DL_ShaFinal
open Aeneas Aeneas.Std Result
namespace R1Z.PV_DL_ShaFinal
set_option autoImplicit false
abbrev State := Array U32 8#usize
abbrev Core := PV_CBL_ShaCore.Core

/-- Owned complete finalizer; the compression backend remains a parameter.
The native block counter is unchanged by finalization. -/
def reference (compress : State → List U8 → Result State) (core : Core)
    (buffer : Array U8 64#usize) (pos : Usize) :
    Result (Core × List U8 × Nat × List U8) := do
  let (state,retained,cursor) ← PV_DL_LengthEncoding.finalize compress core.state
    core.block_len buffer pos
  let out ← PV_DL_ShaSerialize.reference state.val
  ok (⟨state,core.block_len⟩,retained,cursor,out)

def value (compress : State → List U8 → Result State) (core : Core)
    (buffer : Array U8 64#usize) (pos : Usize) :
    Result (Core × List U8 × Nat × List U8) := do
  let state ← PV_DL_CompressionTrace.run compress
    (PV_CBL_PaddingModel.blocks buffer.val pos.val
      (PV_DL_LengthEncoding.suffix (PV_CBL_ShaBitLength.bitLength pos core.block_len)).val) core.state
  ok (⟨state,core.block_len⟩,
    PV_CBL_PaddingModel.first buffer.val pos.val
      (PV_DL_LengthEncoding.suffix (PV_CBL_ShaBitLength.bitLength pos core.block_len)).val,
    0,(PV_DL_ShaSerialize.array state).val)

theorem source_reference (compress : State → List U8 → Result State) (core : Core)
    (buffer : Array U8 64#usize) (pos : Usize) (h : pos.val<64) :
    reference compress core buffer pos=value compress core buffer pos := by
  unfold reference
  rw [PV_DL_LengthEncoding.source compress core.state core.block_len buffer pos h]
  simp only [PV_DL_FinalizeParam.model,bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry]
  unfold value
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro state hs
  rw [PV_DL_ShaSerialize.total]
  rfl

theorem identity_run (events : List (List U8)) (state : State) :
    PV_DL_CompressionTrace.run (fun state _ => ok state) events state=ok state := by
  induction events with
  | nil => rfl
  | cons block tail ih => simp only [PV_DL_CompressionTrace.run,bind_tc_ok,ih]

theorem nonvacuous (core : Core) (buffer : Array U8 64#usize) (pos : Usize)
    (h : pos.val<64) :
    ∃ result, reference (fun state _ => ok state) core buffer pos=ok result := by
  rw [source_reference _ core buffer pos h]
  unfold value
  rw [identity_run]
  exact ⟨_,rfl⟩

#print axioms identity_run
#print axioms nonvacuous
#print axioms reference
#print axioms value
#print axioms source_reference
end R1Z.PV_DL_ShaFinal

end
