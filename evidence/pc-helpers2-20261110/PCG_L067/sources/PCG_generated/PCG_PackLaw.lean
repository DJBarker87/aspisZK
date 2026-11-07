import PCG_PackRef.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCG_PackLaw

theorem word_step (word : U64) (byte : U8) (bound : word.val < 281474976710656) :
 ∃ out, PCG_PackRef.word_step word byte = ok out ∧
 out.val = word.val * 256 + byte.val := by
 obtain ⟨mul,hm,vm⟩ := WP.spec_imp_exists
  (UScalar.mul_spec (x:=word) (y:=256#u64) (by scalar_tac))
 let b := core.convert.num.FromU64U8.from byte
 have vb : b.val = byte.val := by dsimp [b]; scalar_tac
 obtain ⟨out,ho,vo⟩ := WP.spec_imp_exists
  (UScalar.add_spec (x:=mul) (y:=b) (by scalar_tac))
 refine ⟨out,?_,?_⟩
 · simp only [PCG_PackRef.word_step,lift,bind_tc_ok]
   rw [hm]
   exact ho
 · scalar_tac

def word (bytes : List U8) : Nat := bytes.foldl (fun w b => w*256+b.val) 0

/-- Symbolic loop invariant; no concrete seven-byte numeral reduction. -/
theorem fold_bound (bytes : List U8) (w k : Nat) (h : w < 256^k) :
 bytes.foldl (fun w b => w*256+b.val) w < 256^(k+bytes.length) := by
 induction bytes generalizing w k with
 | nil => simpa using h
 | cons b bs ih =>
   have hb : b.val < 256 := by scalar_tac
   have hn : w*256+b.val < 256^(k+1) := by
     rw [Nat.pow_succ]
     omega
   have hh := ih (w*256+b.val) (k+1) hn
   simpa [List.foldl, Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem word_bound (bytes : List U8) : word bytes < 256^bytes.length := by
 simpa [word] using fold_bound bytes 0 0 (by decide)

def readWord (w : U64) : List U8 → Result U64
 | [] => ok w
 | b::bs => do
   let next ← PCG_PackRef.word_step w b
   readWord next bs

theorem power_bound (k : Nat) (h : k ≤ 6) : 256^k ≤ 281474976710656 := by
 interval_cases k <;> decide

/-- Induction from every native loop pre-state; the invariant proves all
machine arithmetic stays within u64 and the next native step's domain. -/
theorem read_suffix (bytes : List U8) (w : U64) (k : Nat)
 (length : k+bytes.length ≤ 7) (bound : w.val < 256^k) :
 ∃ out, readWord w bytes = ok out ∧
 out.val = bytes.foldl (fun x b => x*256+b.val) w.val := by
 induction bytes generalizing w k with
 | nil => exact ⟨w,rfl,rfl⟩
 | cons b bs ih =>
   have ksmall : k ≤ 6 := by simp only [List.length_cons] at length; omega
   obtain ⟨next,hn,vn⟩ := word_step w b (Nat.lt_of_lt_of_le bound (power_bound k ksmall))
   have bsmall : b.val < 256 := by scalar_tac
   have nextBound : next.val < 256^(k+1) := by rw [vn,Nat.pow_succ]; omega
   obtain ⟨out,ho,vo⟩ := ih next (k+1) (by simpa [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using length) nextBound
   exact ⟨out,by simp only [readWord,hn,bind_tc_ok,ho],by simpa only [List.foldl_cons,vn] using vo⟩

def denominator (g : Nat) : Nat :=
 match g with
 | 0 => 562949953421312 | 1 => 4398046511104 | 2 => 34359738368
 | 3 => 268435456 | 4 => 2097152 | 5 => 16384 | 6 => 128 | _ => 1

theorem denominator_positive (g : Nat) : 0 < denominator g := by
 unfold denominator
 split <;> decide

theorem denominator_ref (g : Usize) :
 PCG_PackRef.denominator g = ok (U64.ofNatCore (denominator g.val) (by
  unfold denominator
  split <;> scalar_tac)) := by
 unfold PCG_PackRef.denominator denominator
 split <;> rfl

theorem group_step (word : U64) (g : Usize) :
 ∃ out, PCG_PackRef.group word g = ok out ∧
 out.val = (word.val / denominator g.val) % 128 ∧ out.val < 128 := by
 let d := U64.ofNatCore (denominator g.val) (by
  unfold denominator
  split <;> scalar_tac)
 have hd : d ≠ 0#u64 := by
   have hp := denominator_positive g.val
   intro he
   have hv := congrArg UScalar.val he
   simp only [d,UScalar.val_ofNatCore] at hv
   scalar_tac
 obtain ⟨q,hq,vq⟩ := UScalar.div_spec (x:=word) (y:=d) hd
 obtain ⟨r,hr,vr⟩ := WP.spec_imp_exists
  (UScalar.rem_spec (x:=q) (y:=128#u64) (by decide))
 have small : r.val < 128 := by scalar_tac
 refine ⟨UScalar.cast .U8 r,?_,?_,?_⟩
 · simp only [PCG_PackRef.group,denominator_ref,bind_tc_ok]
   change (do let q ← word / d; let r ← q % 128#u64; ok (UScalar.cast .U8 r)) = _
   rw [hq]
   simp only [bind_tc_ok]
   rw [hr]
   rfl
 · dsimp [d] at vq
   scalar_tac
 · scalar_tac

/-- Arbitrary-index write frame, used for disjoint iteration composition. -/
theorem write_frame (seed : Nat → U8) (offset other : Nat) (value : U8)
 (different : other ≠ offset) : Function.update seed offset value other = seed other := by
 simp [Function.update,different]

/-- Every group of a chunk occupies a distinct position; four chunks cover 32. -/
theorem distinct_windows (c d g h : Nat) (hc : c < 4) (hd : d < 4)
 (hg : g < 8) (hh : h < 8) : 8*c+g=8*d+h ↔ c=d ∧ g=h := by omega

def pack (digest : Array U8 32#usize) : Nat → Nat := fun offset =>
 let c := offset / 8
 let g := offset % 8
 word ((digest.val.drop (7*c)).take 7) / denominator g % 128

/-- Complete packed value model: exact source chunk/group indices, including
unused final four digest bytes. Native iteration/association certificates
supply the machine step; this theorem supplies total byte range and indices. -/
theorem row_293 (digest : Array U8 32#usize) (offset : Nat) (h : offset < 32) :
 pack digest offset < 128 ∧ offset / 8 < 4 ∧ offset % 8 < 8 ∧
 7*(offset/8)+6 < 32 := by
 refine ⟨Nat.mod_lt _ (by decide),?_,Nat.mod_lt _ (by decide),?_⟩ <;> omega

#print axioms word_step
#print axioms fold_bound
#print axioms word_bound
#print axioms power_bound
#print axioms read_suffix
#print axioms denominator_positive
#print axioms denominator_ref
#print axioms group_step
#print axioms write_frame
#print axioms distinct_windows
#print axioms row_293
end PCG_PackLaw
