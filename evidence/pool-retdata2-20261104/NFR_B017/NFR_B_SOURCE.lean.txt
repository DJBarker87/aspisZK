import NFR_DigestForward
set_option autoImplicit false
noncomputable section
namespace NFR_AfterstateForwardHelpers
open Aeneas Aeneas.Std Result WP AspisR1TerminalDecoder
open AspisR1.S2K AspisS6NativeAfterstateEncoderReuse AspisS6SourceCodec
abbrev Afterstate := pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
abbrev Digest := Array U32 8#usize

def encoded (a : Afterstate) : Slice U8 := (AfterstateEncoding.bytes a).to_slice

theorem domain (a : Afterstate)
    (valid : pool_v1.pair_terminal.validate_verified_afterstate a = ok (.Ok ())) :
    NBD_DigestInduction.Canonical a.next_root ∧
    ∀ i : Fin 20, NBD_DigestInduction.Canonical
      (a.next_frontier.val[i.val]'(by have := a.next_frontier.property; scalar_tac)) := by
  rw [NBH_Validators.afterstate] at valid
  unfold NBH_Validators.afterResult at valid
  split at valid
  · cases valid
  · split at valid
    · rename_i h
      exact ⟨h.1,fun i => h.2 i (by omega)⟩
    · cases valid
#print axioms domain

theorem range {N : Usize} (bytes : Slice U8) (start stop : Usize)
    (arr : Array U8 N) (ordered : start.val ≤ stop.val)
    (bounded : stop.val ≤ bytes.val.length)
    (same : List.slice start.val stop.val bytes.val = arr.val) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      bytes {start:=start,«end»:=stop} = ok arr.to_slice := by
  have spec : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      bytes {start:=start,«end»:=stop} ⦃ out => out=arr.to_slice ⦄ := by
    unfold core.slice.index.Slice.index
    step*
    all_goals try scalar_tac
    all_goals apply Subtype.ext
    all_goals exact out_post1.trans same
  obtain ⟨out,run,equal⟩ := WP.spec_imp_exists spec
  exact run.trans (congrArg ok equal)
#print axioms range

theorem uniform_window {T : Type} (f : T → List U8) (n : Nat)
    (width : ∀ x, (f x).length = n) (xs : List T)
    (i : Nat) (bound : i < xs.length) :
    ((xs.flatMap f).drop (n*i)).take n = f xs[i] := by
  induction xs generalizing i with
  | nil => simp at bound
  | cons x xs ih =>
    cases i with
    | zero => simp [List.flatMap_cons,List.take_append,width]
    | succ i =>
      have small : i < xs.length := by simpa using bound
      simpa [List.flatMap_cons,List.drop_append,width,Nat.mul_succ] using ih i small
#print axioms uniform_window

theorem digest_width (d : Digest) : (DigestContents.chunks d).length = 32 :=
  PaymentContents.digest_chunks_length d
#print axioms digest_width

theorem root_window (a : Afterstate) :
    List.slice 16 48 (encoded a).val = (DigestBytes.bytes a.next_root).val := by
  change List.slice 16 48 (AfterstateEncoding.bytes a).val = _
  rw [native_afterstate_contents,native_digest_bytes]
  simp [prefix_bytes,List.slice,List.drop_append,List.take_append,digest_width,
    header_bytes,pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC.property,
    (core.num.U64.to_le_bytes a.next_pair_index).property]
#print axioms root_window

theorem frontier_window (a : Afterstate) (i : Nat) (bound : i < 20) :
    List.slice (48+32*i) (80+32*i) (encoded a).val =
      (DigestBytes.bytes
        (a.next_frontier.val[i]'(by have := a.next_frontier.property; scalar_tac))).val := by
  change List.slice _ _ (AfterstateEncoding.bytes a).val = _
  rw [native_afterstate_contents,native_digest_bytes]
  have small : i < a.next_frontier.val.length := by simpa only [a.next_frontier.property,show (20#usize).val=20 from rfl] using bound
  have prefix_width : (prefix_bytes a).length = 48 := by
    simp [prefix_bytes,header_bytes,digest_width,
      pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC.property,
      (core.num.U64.to_le_bytes a.next_pair_index).property]
  unfold List.slice
  rw [show 80+32*i-(48+32*i)=32 from by omega,List.drop_append,
    List.drop_eq_nil_of_le (by rw [prefix_width]; omega)]
  simp only [List.nil_append,prefix_width,show 48+32*i-48=32*i from by omega]
  exact uniform_window DigestContents.chunks 32 digest_width a.next_frontier.val i small
#print axioms frontier_window
theorem index_window (a : Afterstate) :
    List.slice 8 16 (encoded a).val = (core.num.U64.to_le_bytes a.next_pair_index).val := by
  change List.slice 8 16 (AfterstateEncoding.bytes a).val = _
  rw [native_afterstate_contents]
  simp [prefix_bytes,List.slice,List.drop_append,List.take_append,digest_width,
    header_bytes,pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC.property,
    (core.num.U64.to_le_bytes a.next_pair_index).property]
#print axioms index_window

theorem twenty_eta {T : Type} (a : Array T 20#usize) :
    Array.make 20#usize [a.val[0]'(by rw [a.property]; decide),a.val[1]'(by rw [a.property]; decide),a.val[2]'(by rw [a.property]; decide),a.val[3]'(by rw [a.property]; decide),a.val[4]'(by rw [a.property]; decide),a.val[5]'(by rw [a.property]; decide),a.val[6]'(by rw [a.property]; decide),a.val[7]'(by rw [a.property]; decide),a.val[8]'(by rw [a.property]; decide),a.val[9]'(by rw [a.property]; decide),a.val[10]'(by rw [a.property]; decide),a.val[11]'(by rw [a.property]; decide),a.val[12]'(by rw [a.property]; decide),a.val[13]'(by rw [a.property]; decide),a.val[14]'(by rw [a.property]; decide),a.val[15]'(by rw [a.property]; decide),a.val[16]'(by rw [a.property]; decide),a.val[17]'(by rw [a.property]; decide),a.val[18]'(by rw [a.property]; decide),a.val[19]'(by rw [a.property]; decide)] = a := by
  apply Subtype.ext
  apply List.ext_getElem
  · simp [Array.make,a.property]
  · intro i hi hj
    have small : i < 20 := by simpa only [a.property,show (20#usize).val=20 from rfl] using hj
    interval_cases i <;> rfl
#print axioms twenty_eta
end NFR_AfterstateForwardHelpers
