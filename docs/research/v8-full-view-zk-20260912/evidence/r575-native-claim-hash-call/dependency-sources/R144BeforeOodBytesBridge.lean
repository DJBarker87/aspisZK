import AspisR136BeforeOod.Funs
import Aeneas.Tactic.Step.Step

/-! Symbolic serialization of any bounded QM31 slice.
Each value contributes its four U32 limbs in source order, little endian.
The source loop is proved through its iterator invariant, never by expanding
358 concrete values. This file makes no privacy or soundness claim. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
namespace AspisV8R19.R144BeforeOodBytesBridge
open Aeneas Aeneas.Std Result ControlFlow Error
open Aeneas.Std.WP
open AspisR136BeforeOod

theorem setSlice_halves {A : Type} (out a b : List A) (n : Nat)
    (hout : out.length = n + n) (ha : a.length = n) (hb : b.length = n) :
    List.setSlice! (List.setSlice! out 0 a) n b = a ++ b := by
  unfold List.setSlice!
  simp [hout, ha, hb, List.take_of_length_le, List.drop_of_length_le]

theorem setSlice_zero_full {A : Type} (out bytes : List A)
    (h : out.length = bytes.length) :
    List.setSlice! out 0 bytes = bytes := by
  unfold List.setSlice!
  simp [h, List.take_of_length_le, List.drop_of_length_le]

theorem write_le_bytes_length
    (q : aspis_core.field.QM31) (out : Slice Std.U8)
    (hout : out.length = 16) :
    aspis_core.field.QM31.write_le_bytes q out
      ⦃ r => r.length = out.length ⦄ := by
  unfold aspis_core.field.QM31.write_le_bytes
  unfold AspisR137Transcript.field.QM31.write_le_bytes
  unfold AspisR137Transcript.field.CM31.write_le_bytes
  unfold AspisR137Transcript.field.M31.to_le_bytes
  repeat step
  all_goals simp_all [Array.to_slice, Slice.length]
  all_goals step
  all_goals simp_all [Slice.length, lift, bind_tc_ok]
  all_goals step
  all_goals simp_all [Slice.length, Slice.setSlice!]


def cm31Bytes (q : AspisR137Transcript.field.CM31) : List U8 :=
  (core.num.U32.to_le_bytes q.a).val ++ (core.num.U32.to_le_bytes q.b).val

def qm31Bytes (q : aspis_core.field.QM31) : List U8 :=
  cm31Bytes (toR137QM31 q).c0 ++ cm31Bytes (toR137QM31 q).c1

theorem cm31Bytes_length (q : AspisR137Transcript.field.CM31) :
    (cm31Bytes q).length = 8 := by
  simp [cm31Bytes, Array.length_eq]

theorem qm31Bytes_length (q : aspis_core.field.QM31) :
    (qm31Bytes q).length = 16 := by
  simp [qm31Bytes, cm31Bytes_length]

@[step]
theorem cm31_write_exact (q : AspisR137Transcript.field.CM31)
    (out : Slice U8) (hout : out.length = 8) :
    AspisR137Transcript.field.CM31.write_le_bytes q out
      ⦃ r => r.val = cm31Bytes q ⦄ := by
  unfold AspisR137Transcript.field.CM31.write_le_bytes
  unfold AspisR137Transcript.field.M31.to_le_bytes
  repeat step
  all_goals simp_all [Array.to_slice, Slice.length, lift, bind_tc_ok]
  all_goals simp_all [Slice.length, Slice.setSlice!, cm31Bytes]
  apply setSlice_halves _ _ _ 4 hout <;> simp

@[step]
theorem qm31_write_exact (q : aspis_core.field.QM31)
    (out : Slice U8) (hout : out.length = 16) :
    aspis_core.field.QM31.write_le_bytes q out
      ⦃ r => r.val = qm31Bytes q ⦄ := by
  unfold aspis_core.field.QM31.write_le_bytes
  unfold AspisR137Transcript.field.QM31.write_le_bytes
  repeat step
  all_goals simp_all [Slice.length, Slice.setSlice!, qm31Bytes, cm31Bytes_length]
  apply setSlice_halves _ _ _ 8 hout <;> exact cm31Bytes_length _

theorem setSlice_append_replicate {A : Type} (p c : List A) (z : A)
    (n : Nat) (hc : c.length ≤ n) :
    List.setSlice! (p ++ List.replicate n z) p.length c =
      p ++ c ++ List.replicate (n - c.length) z := by
  unfold List.setSlice!
  simp [List.take_append, List.drop_append, List.length_append,
    List.length_replicate, hc]

theorem flatMap_fixed_length {A B : Type} (f : A → List B) (k : Nat)
    (hf : ∀ x, (f x).length = k) (xs : List A) :
    (xs.flatMap f).length = k * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp [hf, ih, Nat.mul_succ] <;> omega

def packed (xs : List aspis_core.field.QM31) : List U8 := xs.flatMap qm31Bytes

theorem packed_length (xs : List aspis_core.field.QM31) :
    (packed xs).length = 16 * xs.length :=
  flatMap_fixed_length qm31Bytes 16 qm31Bytes_length xs

abbrev Iter := core.iter.adapters.enumerate.Enumerate
  (core.slice.iter.Iter aspis_core.field.QM31)

theorem enum_next_some (v : Slice aspis_core.field.QM31) (iter : Iter)
    (hs : iter.iter.slice = v) (hi : iter.iter.i = iter.count.val)
    (hlt : iter.count.val < v.val.length)
    (hcount : iter.count.val + 1 ≤ Usize.max) :
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter aspis_core.field.QM31) iter
      ⦃ p => p.1 = some (iter.count, v.val[iter.count.val]) ∧
        p.2.iter.slice = v ∧ p.2.iter.i = iter.count.val + 1 ∧
        p.2.count.val = iter.count.val + 1 ⦄ := by
  apply spec_mono (core.iter.adapters.enumerate.IteratorEnumerate.next_some_spec
    _ iter v.val[iter.count.val] { slice := v, i := iter.count.val + 1 } ?_ hcount)
  · rintro ⟨o, iter1⟩ ⟨ho, hit, hc⟩
    exact ⟨ho, congrArg core.slice.iter.Iter.slice hit,
      congrArg core.slice.iter.Iter.i hit, hc⟩
  · simp [core.iter.traits.iterator.IteratorSliceIter,
      core.slice.iter.IteratorSliceIter.next, hs, hi, Slice.len, hlt]

def Inv (v : Slice aspis_core.field.QM31) (p : Iter × alloc.vec.Vec U8) : Prop :=
  p.1.iter.slice = v ∧ p.1.iter.i = p.1.count.val ∧
  p.1.count.val ≤ v.val.length ∧
  p.2.val = packed (v.val.take p.1.count.val) ++
    List.replicate (16 * (v.val.length - p.1.count.val)) 0#u8

theorem inv_length (v : Slice aspis_core.field.QM31)
    (iter : Iter) (b : alloc.vec.Vec U8) (h : Inv v (iter, b)) :
    b.length = 16 * v.val.length := by
  change b.val.length = 16 * v.val.length
  simp only [Inv, Prod.fst, Prod.snd] at h
  rcases h with ⟨_, _, hi, hb⟩
  simp only [hb, List.length_append, packed_length,
    List.length_take, min_eq_left hi, List.length_replicate]
  omega

theorem packed_update (xs : List aspis_core.field.QM31) (i : Nat)
    (hi : i < xs.length) :
    List.setSlice! (packed (xs.take i) ++
      List.replicate (16 * (xs.length - i)) 0#u8) (i * 16) (qm31Bytes xs[i]) =
      packed (xs.take (i+1)) ++ List.replicate (16 * (xs.length - (i+1))) 0#u8 := by
  have hp : (packed (xs.take i)).length = i * 16 := by
    simp [packed_length, List.length_take, Nat.min_eq_left (by omega : i ≤ xs.length),
      Nat.mul_comm]
  have hc : (qm31Bytes xs[i]).length ≤ 16 * (xs.length - i) := by
    rw [qm31Bytes_length]; omega
  have har : 16 * (xs.length - i) - 16 = 16 * (xs.length - (i+1)) := by omega
  rw [← hp, setSlice_append_replicate _ _ _ _ hc, qm31Bytes_length, har,
    List.take_succ_eq_append_getElem hi]
  simp only [packed, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_assoc]

theorem body_inv (v : Slice aspis_core.field.QM31)
    (hsize : 16 * v.val.length ≤ Usize.max)
    (iter : Iter) (b : alloc.vec.Vec U8) (h : Inv v (iter, b)) :
    bytes_loop.body iter b ⦃ r => match r with
      | .done out => out.val = packed v.val
      | .cont p => Inv v p ∧
          v.val.length - p.1.count.val < v.val.length - iter.count.val ⦄ := by
  have hbl := inv_length v iter b h
  simp only [Inv, Prod.fst, Prod.snd] at h
  obtain ⟨hs, hi, hle, hb⟩ := h
  by_cases hlt : iter.count.val < v.val.length
  · have hcount : iter.count.val + 1 ≤ Usize.max := by omega
    unfold bytes_loop.body
    apply spec_bind (enum_next_some v iter hs hi hlt hcount)
    rintro ⟨o, iter1⟩ ⟨ho, hs1, hi1, hc1⟩
    simp_all only [ho, Inv, Slice.length, Slice.setSlice!, packed_length,
      List.length_take, List.length_replicate, Nat.min_eq_left hle]
    have hmul : iter.count.val * 16 ≤ Usize.max := by omega
    have hend : iter.count.val * 16 + 16 ≤ Usize.max := by omega
    step with Usize.mul_spec as ⟨start, hstart⟩ by simpa using hmul
    step with Usize.add_spec as ⟨stop, hstop⟩ by simp_all; omega
    step
    step
    all_goals simp_all [Inv, Slice.length, Slice.setSlice!, packed_length,
      List.length_take, List.length_replicate]
    exact ⟨packed_update v.val iter.count.val hlt, by omega⟩
  · have heq : iter.count.val = v.val.length := by omega
    have hnext : core.iter.adapters.enumerate.IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorSliceIter aspis_core.field.QM31) iter =
          .ok (none, { iter with iter := iter.iter }) := by
      simp [core.iter.adapters.enumerate.IteratorEnumerate.next,
        core.slice.iter.IteratorSliceIter.next, hs, hi, Slice.len, hlt]
    simp only [bytes_loop.body, hnext, bind_tc_ok, spec_ok]
    simpa [heq] using hb

theorem bytes_loop_spec (v : Slice aspis_core.field.QM31)
    (hsize : 16 * v.val.length ≤ Usize.max)
    (iter : Iter) (b : alloc.vec.Vec U8) (h : Inv v (iter, b)) :
    bytes_loop iter b ⦃ out => out.val = packed v.val ⦄ := by
  unfold bytes_loop
  apply loop.spec_decr_nat (fun p => v.val.length - p.1.count.val)
    (Inv v) (fun (out : alloc.vec.Vec U8) => out.val = packed v.val)
    (fun p => bytes_loop.body p.1 p.2) (iter, b)
  · rintro ⟨it, buf⟩ hinv
    apply spec_mono (body_inv v hsize it buf hinv)
    intro r hr
    cases r <;> simpa only using hr
  · exact h

theorem bytes_spec (v : Slice aspis_core.field.QM31)
    (hsize : 16 * v.val.length ≤ Usize.max) :
    bytes v ⦃ out => out.val = packed v.val ⦄ := by
  unfold bytes
  step with Usize.mul_spec as ⟨n, hn⟩
  step
  simp only [core.slice.Slice.iter,
    core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default, bind_tc_ok]
  apply bytes_loop_spec v hsize
  simp_all [Inv, packed, Slice.len, Nat.mul_comm]

theorem bytes_exact (v : Slice aspis_core.field.QM31)
    (hsize : 16 * v.val.length ≤ Usize.max) :
    ∃ out, bytes v = .ok out ∧ out.val = packed v.val :=
  spec_imp_exists (bytes_spec v hsize)

def encoded (v : Slice aspis_core.field.QM31)
    (hsize : 16 * v.val.length ≤ Usize.max) : alloc.vec.Vec U8 :=
  ⟨packed v.val, by simpa only [packed_length] using hsize⟩

theorem bytes_execution (v : Slice aspis_core.field.QM31)
    (hsize : 16 * v.val.length ≤ Usize.max) :
    bytes v = .ok (encoded v hsize) := by
  obtain ⟨out, he, hv⟩ := bytes_exact v hsize
  rw [he]
  congr 1
  exact Subtype.ext hv

theorem prefix358_execution (v : Slice aspis_core.field.QM31)
    (hlen : v.val.length = 358) :
    bytes v = .ok (encoded v (by
      rw [hlen]; have := Usize.cMax_bound; scalar_tac)) :=
  bytes_execution v _

#print axioms write_le_bytes_length
#print axioms cm31_write_exact
#print axioms qm31_write_exact
#print axioms body_inv
#print axioms bytes_loop_spec
#print axioms bytes_spec
#print axioms bytes_exact
#print axioms bytes_execution
#print axioms prefix358_execution
end AspisV8R19.R144BeforeOodBytesBridge
