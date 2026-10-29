import PV_DIAG11_WriteAll
import PV_DIAG10_Requests
set_option autoImplicit false
namespace PV_DIAG11

/-! Metadata at the generic write_all loop. Buffer contents are separate.
Actual fd/path/offset/allocator/entropy/logger request provenance is OPEN.
WorldBlind and the original ChargedBad association belong to other lines.
The V400 source-local result below needs equal initial lengths and a
metadata/reply-only write primitive; neither is asserted for all native calls. -/
open PV_DIAG9
structure WriteCursor where
 offset : Nat
 remaining : Nat
 retries : Nat
 deriving DecidableEq
def advance (c : WriteCursor) (n : Nat) : WriteCursor :=
 ⟨c.offset+n,c.remaining-n,c.retries⟩
def interrupted (c : WriteCursor) : WriteCursor := ⟨c.offset,c.remaining,c.retries+1⟩
def writeRequest (target : List Nat) (align address limit : Nat) (c : WriteCursor) : FaultRequest :=
 ⟨1,target,c.offset,min c.remaining limit,align,address,c.retries⟩

theorem write_request_size (target : List Nat) (align address limit : Nat) (c : WriteCursor) : (writeRequest target align address limit c).size=min c.remaining limit := rfl
#print axioms write_request_size
theorem write_slice_length (a b : List UInt8) (n : Nat) (h : a.length=b.length) : (a.drop n).length=(b.drop n).length := by simp only [List.length_drop,h]
#print axioms write_slice_length
theorem write_progress_offset (c : WriteCursor) (n : Nat) : (advance c n).offset=c.offset+n ∧ (advance c n).remaining=c.remaining-n := ⟨rfl,rfl⟩
#print axioms write_progress_offset
theorem write_interrupted_preserves_buffer (c : WriteCursor) : (interrupted c).offset=c.offset ∧ (interrupted c).remaining=c.remaining ∧ (interrupted c).retries=c.retries+1 := ⟨rfl,rfl,rfl⟩
#print axioms write_interrupted_preserves_buffer
theorem write_request_from_public_cursor {I P : Type} (context : I → P) (c : I → WriteCursor) (publicCursor : ∀ i j, context i=context j → c i=c j) (target : List Nat) (align address limit : Nat) (i j : I) (h : context i=context j) : writeRequest target align address limit (c i)=writeRequest target align address limit (c j) := by rw [publicCursor i j h]
#print axioms write_request_from_public_cursor
theorem writeAll_same_length_metadata {V : Type} (w : List UInt8 → Run V IoError Nat) (d : Run V IoError Unit) (primitive : ∀ (a b : List UInt8), a.length=b.length → w a=w b) (fuel : Nat) (a b : List UInt8) (len : a.length=b.length) : writeAll w d fuel a=writeAll w d fuel b := by
 induction fuel generalizing a b with
 | zero =>
   cases a with
   | nil => cases b with
     | nil => rfl
     | cons y ys => simp at len
   | cons x xs => cases b with
     | nil => simp at len
     | cons y ys => rfl
 | succ fuel ih =>
   cases a with
   | nil => cases b with
     | nil => rfl
     | cons y ys => simp at len
   | cons x xs => cases b with
     | nil => simp at len
     | cons y ys =>
       have same := primitive (x::xs) (y::ys) len
       cases hw : w (x::xs) with
       | mk es ex =>
         have hb : w (y::ys)=⟨es,ex⟩ := same.symm.trans hw
         cases ex with
         | ok n =>
           cases n with
           | zero => simp only [writeAll,hw,hb]
           | succ n =>
             have hd := write_slice_length (x::xs) (y::ys) (n+1) len
             simp only [writeAll,hw,hb]
             rw [len,ih _ _ hd]
         | error e =>
           cases e with
           | interrupted =>
             simp only [writeAll,hw,hb]
             rw [ih _ _ len]
           | writeZero => simp only [writeAll,hw,hb]
           | other code => simp only [writeAll,hw,hb]
         | panic => simp only [writeAll,hw,hb]
         | oom => simp only [writeAll,hw,hb]
         | abort => simp only [writeAll,hw,hb]
         | diverge => simp only [writeAll,hw,hb]
#print axioms writeAll_same_length_metadata
theorem writeAll_metadata_public {I P V : Type} (context : I → P) (buf : I → List UInt8) (lengths : ∀ i j, context i=context j → (buf i).length=(buf j).length) (w : List UInt8 → Run V IoError Nat) (d : Run V IoError Unit) (primitive : ∀ (a b : List UInt8), a.length=b.length → w a=w b) (fuel : Nat) (i j : I) (h : context i=context j) : writeAll w d fuel (buf i)=writeAll w d fuel (buf j) := writeAll_same_length_metadata w d primitive fuel _ _ (lengths i j h)
#print axioms writeAll_metadata_public
end PV_DIAG11
