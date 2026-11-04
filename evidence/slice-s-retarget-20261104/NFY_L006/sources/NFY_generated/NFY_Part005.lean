import Lean
import Aeneas
import AspisR1TerminalDecoder.Funs
import NFS_AccumPart01
import NBG_Atomic
import NBP_Read
import NBH_Frontier
import NBH_ArrayEq

-- BEGIN copied NBG_Utilities: lean/NBG_Utilities.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBG_Utilities
open Aeneas Aeneas.Std Result
def pack {α : Type} (a b c d e f g h : α) : Array α 8#usize :=
  Array.make 8#usize [a,b,c,d,e,f,g,h]

theorem shape {α : Type} (a : Array α 8#usize) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7, a=pack a0 a1 a2 a3 a4 a5 a6 a7 := by
  rcases a with ⟨xs,h⟩
  change xs.length=8 at h
  cases xs with
  | nil => simp at h
  | cons a0 xs =>
    cases xs with
    | nil => simp at h
    | cons a1 xs =>
      cases xs with
      | nil => simp at h
      | cons a2 xs =>
        cases xs with
        | nil => simp at h
        | cons a3 xs =>
          cases xs with
          | nil => simp at h
          | cons a4 xs =>
            cases xs with
            | nil => simp at h
            | cons a5 xs =>
              cases xs with
              | nil => simp at h
              | cons a6 xs =>
                cases xs with
                | nil => simp at h
                | cons a7 xs =>
                  cases xs with
                  | nil => exact ⟨a0,a1,a2,a3,a4,a5,a6,a7,rfl⟩
                  | cons a8 xs => simp at h

theorem lists (xs ys : List U8) (width : xs.length=ys.length) :
    List.allM (fun (x,y) => do let b ← core.cmp.PartialEqU8.ne x y;ok (¬ b))
      (xs.zip ys)=ok (decide (xs=ys)) := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil=>rfl
    | cons y ys=>simp only [List.length_nil,List.length_cons] at width;omega
  | cons x xs ih =>
    cases ys with
    | nil=>simp only [List.length_nil,List.length_cons] at width;omega
    | cons y ys=>
      have tail : xs.length=ys.length := Nat.succ.inj width
      by_cases same : x=y
      · subst y
        have comp : core.cmp.impls.PartialEqU8.ne x x=false := by
          simp [core.cmp.impls.PartialEqU8.ne]
        simp only [List.zip_cons_cons,List.allM,comp,bind_tc_ok]
        change List.allM _ (xs.zip ys)=ok (decide (x::xs=x::ys))
        simpa only [List.cons.injEq,true_and,liftFun2,bind_tc_ok] using ih ys tail
      · have comp : core.cmp.impls.PartialEqU8.ne x y=true := by
          simp [core.cmp.impls.PartialEqU8.ne,same]
        simp only [List.zip_cons_cons,List.allM,comp,bind_tc_ok]
        change ok false=ok (decide (x::xs=y::ys))
        simp [same]

#print axioms shape
#print axioms lists
end NFY_NBG_Utilities
-- END copied NBG_Utilities
-- BEGIN copied NBG_Header: lean/NBG_Header.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBG_Header
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev K := pool_v1.historical_anchor.PoolV1TransitionKind
abbrev E := pool_v1.payment_relation.PoolV1PaymentStatementFormatError

def tag : K → U8 | .PrivateTransfer => 1#u8 | .Withdrawal => 2#u8

theorem tag_result (kind : K) :
    UScalar.cast .U8 (read_discriminant kind : U8) = tag kind := by
  cases kind <;> rfl

theorem slice_equal (a b : Slice U8) (width : a.val.length = b.val.length) :
    core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 a b =
      ok (decide (a.val = b.val)) := by
  unfold core.slice.cmp.PartialEqSlice.eq
  rw [if_pos width]
  exact NFY_NBG_Utilities.lists a.val b.val width

def expected (bytes : Array U8 216#usize) (magic : Array U8 4#usize)
    (kind : K) : core.result.Result Unit E :=
  if bytes.val.take 4 ≠ magic.val then .Err .WrongMagic
  else if bytes.val[4]! ≠ 1#u8 then .Err .WrongVersion
  else if bytes.val[5]! ≠ tag kind then .Err .WrongTransitionKind
  else if bytes.val[6]! ≠ 1#u8 then .Err .WrongDigestEncoding
  else if bytes.val[7]! ≠ 0#u8 then .Err .NonZeroReserved
  else .Ok ()

theorem header_result (bytes : Array U8 216#usize) (magic : Array U8 4#usize)
    (kind : K) :
    pool_v1.payment_relation.require_header bytes magic kind = ok (expected bytes magic kind) := by
  simp [pool_v1.payment_relation.require_header,
    core.array.Array.index,core.ops.index.IndexSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index,
    core.slice.index.SliceIndexRangeUsizeSlice.index,
    Slice.len,Slice.length,Array.to_slice,bytes.property,magic.property,
    core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
    AspisR1TerminalDecoder.Slice.Insts.CoreCmpPartialEqSlice,slice_equal,
    Array.index_usize,tag_result,lift,bind_tc_ok,
    pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION,
    pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,expected]
  repeat' split
  all_goals simp_all

#print axioms tag_result
#print axioms slice_equal
#print axioms header_result
end NFY_NBG_Header
-- END copied NBG_Header
-- BEGIN copied NBG_WideBytes: lean/NBG_WideBytes.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBG_WideBytes
open Aeneas Aeneas.Std Result
abbrev NE := FIo_Native.aspis_core.field.wide_exact.WideExact

def word (bytes : Array U8 32#usize) (i : Nat) : U32 :=
  core.num.U32.from_le_bytes (Array.make 4#usize
    [bytes.val[4*i]!,bytes.val[4*i+1]!,bytes.val[4*i+2]!,bytes.val[4*i+3]!])

def limbs (bytes : Array U8 32#usize) : Array U32 8#usize :=
  Array.make 8#usize [word bytes 0,word bytes 1,word bytes 2,word bytes 3,
    word bytes 4,word bytes 5,word bytes 6,word bytes 7]

/-- Every input byte is retained in the correct little-endian word. Rejection
and successful carriers are then exactly NFS_NBG_WideCarriers.limbs_result. -/
theorem bytes_result (bytes : Array U8 32#usize) :
    FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes bytes.to_slice =
      FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs (limbs bytes) := by
  simp [FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes,
    FIo_Native.aspis_core.field.wide_exact.WideExact.BYTE_LEN,
    Slice.index_usize,Array.to_slice,Slice.len,Slice.length,bytes.property,
    limbs,word,lift,bind_tc_ok]

#print axioms bytes_result
end NFY_NBG_WideBytes
-- END copied NBG_WideBytes
-- BEGIN copied NBP_DecodeWord: lean/NBP_DecodeWord.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBP_DecodeWord
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev word := NFY_NBG_WideBytes.word
abbrev P : U32 := 2147483647#u32
/-- The first rejecting word stops before any later word is decoded. -/
theorem reject0 (bytes : Array U8 32#usize) (h0 : word bytes 0 >= P) :
    atomic_statement.decode_digest_canonical bytes =
      ok (.Err .NonCanonicalDigest) := by
  have len : bytes.val.length = 32 := by simpa using bytes.property
  simp [word,NFY_NBG_WideBytes.word,P, len] at h0
  simp [atomic_statement.decode_digest_canonical,Array.index_usize,
    Array.length,bytes.property,NBG_Atomic.m31_decode,h0,
    core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame]
#print axioms reject0
end NFY_NBP_DecodeWord
-- END copied NBP_DecodeWord
-- BEGIN copied NBP_Decode1: lean/NBP_Decode1.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBP_Decode1
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NFY_NBP_DecodeWord
theorem result (bytes : Array U8 32#usize)
    (h0 : word bytes 0 < P)
    (h1 : word bytes 1 >= P) :
    atomic_statement.decode_digest_canonical bytes = ok (.Err .NonCanonicalDigest) := by
  have len : bytes.val.length = 32 := by simpa using bytes.property
  simp [word,NFY_NBG_WideBytes.word,P,len] at h0 h1
  simp [atomic_statement.decode_digest_canonical,Array.index_usize,
    bytes.property,NBG_Atomic.m31_decode,
    core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame,not_le.mpr h0,h1]
#print axioms result
end NFY_NBP_Decode1
-- END copied NBP_Decode1
-- BEGIN copied NBP_Decode2: lean/NBP_Decode2.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBP_Decode2
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NFY_NBP_DecodeWord
theorem result (bytes : Array U8 32#usize)
    (h0 : word bytes 0 < P)
    (h1 : word bytes 1 < P)
    (h2 : word bytes 2 >= P) :
    atomic_statement.decode_digest_canonical bytes = ok (.Err .NonCanonicalDigest) := by
  have len : bytes.val.length = 32 := by simpa using bytes.property
  simp [word,NFY_NBG_WideBytes.word,P,len] at h0 h1 h2
  simp [atomic_statement.decode_digest_canonical,Array.index_usize,
    bytes.property,NBG_Atomic.m31_decode,
    core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame,not_le.mpr h0,not_le.mpr h1,h2]
#print axioms result
end NFY_NBP_Decode2
-- END copied NBP_Decode2
-- BEGIN copied NBP_Decode3: lean/NBP_Decode3.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBP_Decode3
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NFY_NBP_DecodeWord
theorem result (bytes : Array U8 32#usize)
    (h0 : word bytes 0 < P)
    (h1 : word bytes 1 < P)
    (h2 : word bytes 2 < P)
    (h3 : word bytes 3 >= P) :
    atomic_statement.decode_digest_canonical bytes = ok (.Err .NonCanonicalDigest) := by
  have len : bytes.val.length = 32 := by simpa using bytes.property
  simp [word,NFY_NBG_WideBytes.word,P,len] at h0 h1 h2 h3
  simp [atomic_statement.decode_digest_canonical,Array.index_usize,
    bytes.property,NBG_Atomic.m31_decode,
    core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame,not_le.mpr h0,not_le.mpr h1,not_le.mpr h2,h3]
#print axioms result
end NFY_NBP_Decode3
-- END copied NBP_Decode3
-- BEGIN copied NBP_Decode4: lean/NBP_Decode4.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBP_Decode4
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NFY_NBP_DecodeWord
theorem result (bytes : Array U8 32#usize)
    (h0 : word bytes 0 < P)
    (h1 : word bytes 1 < P)
    (h2 : word bytes 2 < P)
    (h3 : word bytes 3 < P)
    (h4 : word bytes 4 >= P) :
    atomic_statement.decode_digest_canonical bytes = ok (.Err .NonCanonicalDigest) := by
  have len : bytes.val.length = 32 := by simpa using bytes.property
  simp [word,NFY_NBG_WideBytes.word,P,len] at h0 h1 h2 h3 h4
  simp [atomic_statement.decode_digest_canonical,Array.index_usize,
    bytes.property,NBG_Atomic.m31_decode,
    core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame,not_le.mpr h0,not_le.mpr h1,not_le.mpr h2,not_le.mpr h3,h4]
#print axioms result
end NFY_NBP_Decode4
-- END copied NBP_Decode4
-- BEGIN copied NBP_Decode5: lean/NBP_Decode5.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBP_Decode5
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NFY_NBP_DecodeWord
theorem result (bytes : Array U8 32#usize)
    (h0 : word bytes 0 < P)
    (h1 : word bytes 1 < P)
    (h2 : word bytes 2 < P)
    (h3 : word bytes 3 < P)
    (h4 : word bytes 4 < P)
    (h5 : word bytes 5 >= P) :
    atomic_statement.decode_digest_canonical bytes = ok (.Err .NonCanonicalDigest) := by
  have len : bytes.val.length = 32 := by simpa using bytes.property
  simp [word,NFY_NBG_WideBytes.word,P,len] at h0 h1 h2 h3 h4 h5
  simp [atomic_statement.decode_digest_canonical,Array.index_usize,
    bytes.property,NBG_Atomic.m31_decode,
    core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame,not_le.mpr h0,not_le.mpr h1,not_le.mpr h2,not_le.mpr h3,not_le.mpr h4,h5]
#print axioms result
end NFY_NBP_Decode5
-- END copied NBP_Decode5
-- BEGIN copied NBP_Decode6: lean/NBP_Decode6.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBP_Decode6
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NFY_NBP_DecodeWord
theorem result (bytes : Array U8 32#usize)
    (h0 : word bytes 0 < P)
    (h1 : word bytes 1 < P)
    (h2 : word bytes 2 < P)
    (h3 : word bytes 3 < P)
    (h4 : word bytes 4 < P)
    (h5 : word bytes 5 < P)
    (h6 : word bytes 6 >= P) :
    atomic_statement.decode_digest_canonical bytes = ok (.Err .NonCanonicalDigest) := by
  have len : bytes.val.length = 32 := by simpa using bytes.property
  simp [word,NFY_NBG_WideBytes.word,P,len] at h0 h1 h2 h3 h4 h5 h6
  simp [atomic_statement.decode_digest_canonical,Array.index_usize,
    bytes.property,NBG_Atomic.m31_decode,
    core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame,not_le.mpr h0,not_le.mpr h1,not_le.mpr h2,not_le.mpr h3,not_le.mpr h4,not_le.mpr h5,h6]
#print axioms result
end NFY_NBP_Decode6
-- END copied NBP_Decode6
-- BEGIN copied NBP_Decode7: lean/NBP_Decode7.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBP_Decode7
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NFY_NBP_DecodeWord
theorem result (bytes : Array U8 32#usize)
    (h0 : word bytes 0 < P)
    (h1 : word bytes 1 < P)
    (h2 : word bytes 2 < P)
    (h3 : word bytes 3 < P)
    (h4 : word bytes 4 < P)
    (h5 : word bytes 5 < P)
    (h6 : word bytes 6 < P)
    (h7 : word bytes 7 >= P) :
    atomic_statement.decode_digest_canonical bytes = ok (.Err .NonCanonicalDigest) := by
  have len : bytes.val.length = 32 := by simpa using bytes.property
  simp [word,NFY_NBG_WideBytes.word,P,len] at h0 h1 h2 h3 h4 h5 h6 h7
  simp [atomic_statement.decode_digest_canonical,Array.index_usize,
    bytes.property,NBG_Atomic.m31_decode,
    core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame,not_le.mpr h0,not_le.mpr h1,not_le.mpr h2,not_le.mpr h3,not_le.mpr h4,not_le.mpr h5,not_le.mpr h6,h7]
#print axioms result
end NFY_NBP_Decode7
-- END copied NBP_Decode7
-- BEGIN copied NBP_DecodeSuccess: lean/NBP_DecodeSuccess.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBP_DecodeSuccess
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NFY_NBP_DecodeWord
theorem result (bytes : Array U8 32#usize)
    (h0 : word bytes 0 < P)
    (h1 : word bytes 1 < P)
    (h2 : word bytes 2 < P)
    (h3 : word bytes 3 < P)
    (h4 : word bytes 4 < P)
    (h5 : word bytes 5 < P)
    (h6 : word bytes 6 < P)
    (h7 : word bytes 7 < P) :
    atomic_statement.decode_digest_canonical bytes = ok (.Ok (NFY_NBG_WideBytes.limbs bytes)) := by
  have len : bytes.val.length = 32 := by simpa using bytes.property
  simp [word,NFY_NBG_WideBytes.word,P,len] at h0 h1 h2 h3 h4 h5 h6 h7
  simp [atomic_statement.decode_digest_canonical,Array.index_usize,
    bytes.property,NBG_Atomic.m31_decode,
    core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame,not_le.mpr h0,not_le.mpr h1,not_le.mpr h2,not_le.mpr h3,not_le.mpr h4,not_le.mpr h5,not_le.mpr h6,not_le.mpr h7,NFY_NBG_WideBytes.limbs,NFY_NBG_WideBytes.word,len]
#print axioms result
end NFY_NBP_DecodeSuccess
-- END copied NBP_DecodeSuccess
-- BEGIN copied NBP_DigestDecode: lean/NBP_DigestDecode.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBP_DigestDecode
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NFY_NBP_DecodeWord
/-- Source order, including all noncanonical rejections. -/
def decoded (bytes : Array U8 32#usize) :
    core.result.Result (Array U32 8#usize) atomic_statement.AtomicStatementError :=
  if word bytes 0 >= P then .Err .NonCanonicalDigest else
  if word bytes 1 >= P then .Err .NonCanonicalDigest else
  if word bytes 2 >= P then .Err .NonCanonicalDigest else
  if word bytes 3 >= P then .Err .NonCanonicalDigest else
  if word bytes 4 >= P then .Err .NonCanonicalDigest else
  if word bytes 5 >= P then .Err .NonCanonicalDigest else
  if word bytes 6 >= P then .Err .NonCanonicalDigest else
  if word bytes 7 >= P then .Err .NonCanonicalDigest else
  .Ok (NFY_NBG_WideBytes.limbs bytes)

theorem result (bytes : Array U8 32#usize) :
    atomic_statement.decode_digest_canonical bytes = ok (decoded bytes) := by
  by_cases h0 : word bytes 0 >= P
  · simpa [decoded,h0,if_pos] using NFY_NBP_DecodeWord.reject0 bytes h0
  ·
    by_cases h1 : word bytes 1 >= P
    · simpa [decoded,h0,if_neg,h1,if_pos] using NFY_NBP_Decode1.result bytes (lt_of_not_ge h0) h1
    ·
      by_cases h2 : word bytes 2 >= P
      · simpa [decoded,h0,if_neg,h1,if_neg,h2,if_pos] using NFY_NBP_Decode2.result bytes (lt_of_not_ge h0) (lt_of_not_ge h1) h2
      ·
        by_cases h3 : word bytes 3 >= P
        · simpa [decoded,h0,if_neg,h1,if_neg,h2,if_neg,h3,if_pos] using NFY_NBP_Decode3.result bytes (lt_of_not_ge h0) (lt_of_not_ge h1) (lt_of_not_ge h2) h3
        ·
          by_cases h4 : word bytes 4 >= P
          · simpa [decoded,h0,if_neg,h1,if_neg,h2,if_neg,h3,if_neg,h4,if_pos] using NFY_NBP_Decode4.result bytes (lt_of_not_ge h0) (lt_of_not_ge h1) (lt_of_not_ge h2) (lt_of_not_ge h3) h4
          ·
            by_cases h5 : word bytes 5 >= P
            · simpa [decoded,h0,if_neg,h1,if_neg,h2,if_neg,h3,if_neg,h4,if_neg,h5,if_pos] using NFY_NBP_Decode5.result bytes (lt_of_not_ge h0) (lt_of_not_ge h1) (lt_of_not_ge h2) (lt_of_not_ge h3) (lt_of_not_ge h4) h5
            ·
              by_cases h6 : word bytes 6 >= P
              · simpa [decoded,h0,if_neg,h1,if_neg,h2,if_neg,h3,if_neg,h4,if_neg,h5,if_neg,h6,if_pos] using NFY_NBP_Decode6.result bytes (lt_of_not_ge h0) (lt_of_not_ge h1) (lt_of_not_ge h2) (lt_of_not_ge h3) (lt_of_not_ge h4) (lt_of_not_ge h5) h6
              ·
                by_cases h7 : word bytes 7 >= P
                · simpa [decoded,h0,if_neg,h1,if_neg,h2,if_neg,h3,if_neg,h4,if_neg,h5,if_neg,h6,if_neg,h7,if_pos] using NFY_NBP_Decode7.result bytes (lt_of_not_ge h0) (lt_of_not_ge h1) (lt_of_not_ge h2) (lt_of_not_ge h3) (lt_of_not_ge h4) (lt_of_not_ge h5) (lt_of_not_ge h6) h7
                · simpa [decoded,h0,if_neg,h1,if_neg,h2,if_neg,h3,if_neg,h4,if_neg,h5,if_neg,h6,if_neg,h7,if_neg] using NFY_NBP_DecodeSuccess.result bytes (lt_of_not_ge h0) (lt_of_not_ge h1) (lt_of_not_ge h2) (lt_of_not_ge h3) (lt_of_not_ge h4) (lt_of_not_ge h5) (lt_of_not_ge h6) (lt_of_not_ge h7)

#print axioms result
end NFY_NBP_DigestDecode
-- END copied NBP_DigestDecode
-- BEGIN copied NEQ_DecodeScalar: evidence/slice-s-compose6-20261102/NEQ_DecodeScalar.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEQ_DecodeScalar
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

theorem header_result_state_effects {State : Type} (bytes : Array U8 216#usize)
    (magic : Array U8 4#usize) (kind : NFY_NBG_Header.K) (state : State) :
    (pool_v1.payment_relation.require_header bytes magic kind,state,([] : List Unit)) =
      (ok (NFY_NBG_Header.expected bytes magic kind),state,[]) :=
  congrArg (fun x => (x,state,([] : List Unit))) (NFY_NBG_Header.header_result bytes magic kind)

theorem m31_result_state_effects {State : Type} (bytes : Array U8 4#usize) (state : State) :
    (aspis_core.field.M31.from_le_bytes bytes,state,([] : List Unit)) =
      (ok (let word := core.num.U32.from_le_bytes bytes
        if word >= 2147483647#u32 then none else some word),state,[]) :=
  congrArg (fun x => (x,state,([] : List Unit))) (NBG_Atomic.m31_decode bytes)

theorem digest_result_state_effects {State : Type} (bytes : Array U8 32#usize) (state : State) :
    (atomic_statement.decode_digest_canonical bytes,state,([] : List Unit)) =
      (ok (NFY_NBP_DigestDecode.decoded bytes),state,[]) :=
  congrArg (fun x => (x,state,([] : List Unit))) (NFY_NBP_DigestDecode.result bytes)

/-- Every actual unrolled word call passes these exact four SAME original bytes. -/
theorem digest_word_domain (bytes : Array U8 32#usize) (i : Nat) (bound : i<8) :
    ∃ word : Array U8 4#usize,
      word.val = (bytes.val.drop (4*i)).take 4 ∧ word.val.length=4 := by
  let word : Array U8 4#usize := NBP_Read.chunk bytes (4*i) (by change 4*i+4≤32;omega)
  exact ⟨word,rfl,word.property⟩

#print axioms header_result_state_effects
#print axioms m31_result_state_effects
#print axioms digest_result_state_effects
#print axioms digest_word_domain
end NFY_NEQ_DecodeScalar
-- END copied NEQ_DecodeScalar
-- BEGIN copied NBG_PaymentChecks: lean/NBG_PaymentChecks.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBG_PaymentChecks
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev C := pool_v1.payment_relation.CommonPublicV1
abbrev E := pool_v1.payment_relation.PoolV1PaymentStatementFormatError

def canonical (d : Array U32 8#usize) : Bool :=
  d.val.all (fun x => decide (x.val < 2147483647))

theorem canonical_result (d : Array U32 8#usize) :
    pool_v1.payment_relation.digest_is_canonical d = ok (canonical d) := by
  obtain ⟨a,b,c,e,f,g,h,i,same⟩ := NFY_NBG_Utilities.shape d
  subst d
  unfold NFY_NBG_Utilities.pack
  rw [NBG_Atomic.digest_canonical]
  simp [canonical,NFY_NBG_Utilities.pack,Array.make]

def zero (a : Array U8 32#usize) : Bool := decide (a.val = List.replicate 32 0#u8)

theorem zero_result (a : Array U8 32#usize) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a
      (Array.repeat 32#usize 0#u8) = ok (zero a) := by
  unfold core.array.equality.PartialEqArray.eq
  rw [if_pos (a.property.trans (Array.repeat 32#usize 0#u8).property.symm)]
  rw [NFY_NBG_Utilities.lists a.val (Array.repeat 32#usize 0#u8).val
    (a.property.trans (Array.repeat 32#usize 0#u8).property.symm)]
  rfl

theorem capacity_result : pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY =
    ok 1048576#u64 := by
  unfold pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY pool_v1.format.POOL_V1_TREE_DEPTH
  rfl

def common (c : C) : core.result.Result Unit E :=
  if zero c.pool || zero c.deployment_domain then .Err .ZeroRequiredBinding
  else if c.anchor_sequence.val > 1048576 then .Err .InvalidAnchorSequence
  else if !canonical c.anchor_root || !canonical c.nullifier then .Err .NonCanonicalDigest
  else if c.asset_id.val >= 2147483647 then .Err .NonCanonicalAssetId
  else .Ok ()

theorem common_result (c : C) :
    pool_v1.payment_relation.validate_common c = ok (common c) := by
  simp [pool_v1.payment_relation.validate_common,zero_result,capacity_result,
    canonical_result,common,aspis_core.field.P]
  repeat' split
  all_goals simp_all

#print axioms canonical_result
#print axioms zero_result
#print axioms capacity_result
#print axioms common_result
end NFY_NBG_PaymentChecks
-- END copied NBG_PaymentChecks
-- BEGIN copied NBP_CommonDecode: lean/NBP_CommonDecode.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBP_CommonDecode
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev C := pool_v1.payment_relation.CommonPublicV1
abbrev E := pool_v1.payment_relation.PoolV1PaymentStatementFormatError

def asset (b : Array U8 216#usize) : U32 :=
  core.num.U32.from_le_bytes (NBP_Read.chunk (W:=4#usize) b 144 (by decide))

def common (b : Array U8 216#usize) (anchor nullifier : Array U32 8#usize) : C :=
  ⟨NBP_Read.chunk b 8 (by decide),NBP_Read.chunk b 40 (by decide),
    core.num.U64.from_le_bytes (NBP_Read.chunk b 72 (by decide)),anchor,nullifier,asset b⟩

def decoded (b : Array U8 216#usize) : core.result.Result C E :=
  if asset b >= 2147483647#u32 then .Err .NonCanonicalAssetId else
  match NFY_NBP_DigestDecode.decoded (NBP_Read.chunk b 80 (by decide)) with
  | .Err _ => .Err .NonCanonicalDigest
  | .Ok anchor =>
    match NFY_NBP_DigestDecode.decoded (NBP_Read.chunk b 112 (by decide)) with
    | .Err _ => .Err .NonCanonicalDigest
    | .Ok nullifier =>
      let c := common b anchor nullifier
      match NFY_NBG_PaymentChecks.common c with
      | .Err e => .Err e
      | .Ok () => .Ok c

theorem result (b : Array U8 216#usize) :
    pool_v1.payment_relation.decode_common b = ok (decoded b) := by
  simp [pool_v1.payment_relation.decode_common,
    pool_v1.payment_relation.ASSET_ID_OFFSET,pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET,
    pool_v1.payment_relation.POOL_OFFSET,pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET,
    pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET,pool_v1.payment_relation.ANCHOR_ROOT_OFFSET,
    pool_v1.payment_relation.NULLIFIER_OFFSET,
    core.array.Array.index,core.ops.index.IndexSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index,Array.to_slice,Slice.length,Slice.len,b.property,
    core.array.TryFromArrayCopySlice.try_from,core.array.TryFromSharedArraySlice.try_from,
    atomic_statement.unwrap_fixed_slice,aspis_core.field.P,
    NFY_NBP_DigestDecode.result,NFY_NBG_PaymentChecks.common_result,
    asset,common,decoded,NBP_Read.chunk,lift,bind_tc_ok,List.slice,
    core.result.Result.map_err,
    pool_v1.payment_relation.decode_common.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError,
    pool_v1.payment_relation.decode_common.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once,
    pool_v1.payment_relation.decode_common.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError,
    pool_v1.payment_relation.decode_common.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame]
  repeat' split
  all_goals simp_all
#print axioms result
end NFY_NBP_CommonDecode
-- END copied NBP_CommonDecode
-- BEGIN copied NBH_LiveFrontier: lean/NBH_LiveFrontier.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBH_LiveFrontier
open Aeneas Aeneas.Std Result WP AspisR1TerminalDecoder
open NBD_DigestInduction
attribute [local instance] Classical.propDecidable
open NBH_Frontier

theorem live_loop (a : Frontier) :
    pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1_loop a 0#usize =
    ok (if CanonicalFrom a 0 then .Ok () else .Err .NonCanonicalDigest) := by
  have spec : pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1_loop a 0#usize
      ⦃ r => r = if CanonicalFrom a 0 then .Ok () else .Err .NonCanonicalDigest ⦄ := by
    unfold pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1_loop
    refine loop.spec_decr_nat (fun i : Usize => 20-i.val)
      (fun i : Usize => i.val ≤ 20 ∧ (CanonicalFrom a 0 ↔ CanonicalFrom a i.val))
      (fun r => r = if CanonicalFrom a 0 then .Ok () else .Err .NonCanonicalDigest)
      (fun i => pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1_loop.body a i) 0#usize ?_ ?_
    · intro i hi
      rcases hi with ⟨bound,eqv⟩
      unfold pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1_loop.body
      simp only [NBD_DigestInduction.source]
      step*
      all_goals simp_all [CanonicalFrom]
      all_goals first | scalar_tac | skip
      · refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        constructor
        · intro h j hj; exact h j (by omega)
        · intro h j hj
          by_cases same : j.val = i.val
          · simpa only [same] using (show Canonical (a.val[i.val]'(by have := a.property; scalar_tac)) from by assumption)
          · exact h j (by omega)
      · refine ⟨⟨i.val, by scalar_tac⟩, Nat.le_refl _, ?_⟩
        assumption
    · exact ⟨by scalar_tac, Iff.rfl⟩
  obtain ⟨r,call,same⟩ := WP.spec_imp_exists spec
  rw [same] at call
  exact call

#print axioms live_loop
end NFY_NBH_LiveFrontier
-- END copied NBH_LiveFrontier
-- BEGIN copied NBH_Validators: lean/NBH_Validators.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBH_Validators
open Aeneas Aeneas.Std Result WP AspisR1TerminalDecoder
open NBD_DigestInduction NBH_Frontier
attribute [local instance] Classical.propDecidable
abbrev Afterstate := pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
abbrev AfterError := pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1

def afterResult (a : Afterstate) : core.result.Result Unit AfterError :=
  if a.next_pair_index.val = 0 ∨ 1048576 < a.next_pair_index.val then .Err .InvalidAfterstateIndex
  else if Canonical a.next_root ∧ CanonicalFrom a.next_frontier 0 then .Ok ()
  else .Err .NonCanonicalAfterstate

theorem afterstate (a : Afterstate) :
    pool_v1.pair_terminal.validate_verified_afterstate a = ok (afterResult a) := by
  have spec : pool_v1.pair_terminal.validate_verified_afterstate a
      ⦃ r => r = afterResult a ⦄ := by
    unfold pool_v1.pair_terminal.validate_verified_afterstate
    rw [NBD_DigestInduction.source, NBH_Frontier.afterstate_loop]
    unfold pool_v1.pair_tree_profile.POOL_V1_PAIR_CAPACITY
      pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_DEPTH pool_v1.format.POOL_V1_TREE_DEPTH
    step*
    all_goals simp_all [afterResult]
    all_goals scalar_tac
  obtain ⟨r,call,same⟩ := WP.spec_imp_exists spec
  rw [same] at call
  exact call

#print axioms afterstate
end NFY_NBH_Validators
-- END copied NBH_Validators
-- BEGIN copied NBH_LiveValidator: lean/NBH_LiveValidator.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBH_LiveValidator
open Aeneas Aeneas.Std Result WP AspisR1TerminalDecoder
open NBD_DigestInduction NBH_Frontier
attribute [local instance] Classical.propDecidable
abbrev Snapshot := pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1
abbrev Error := pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1

def result (s : Snapshot) : core.result.Result Unit Error :=
  if s.pool = Array.repeat 32#usize 0#u8 ∨ s.deployment_domain = Array.repeat 32#usize 0#u8 then .Err .ZeroRequiredBinding
  else if s.sequence ≠ s.next_pair_index then .Err .SequenceIndexMismatch
  else if 1048576 ≤ s.next_pair_index.val then .Err .TreeFull
  else if Canonical s.current_root ∧ CanonicalFrom s.frontier 0 then .Ok ()
  else .Err .NonCanonicalDigest

theorem source (s : Snapshot) :
    pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1 s = ok (result s) := by
  have spec : pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1 s
      ⦃ r => r = result s ⦄ := by
    unfold pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1
    rw [NBD_DigestInduction.source, NFY_NBH_LiveFrontier.live_loop]
    simp only [NBH_ArrayEq.source]
    unfold pool_v1.pair_tree_profile.POOL_V1_PAIR_CAPACITY
      pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_DEPTH pool_v1.format.POOL_V1_TREE_DEPTH
    step*
    all_goals simp_all [result]
    all_goals scalar_tac
  obtain ⟨r,call,same⟩ := WP.spec_imp_exists spec
  rw [same] at call
  exact call

#print axioms source
end NFY_NBH_LiveValidator
-- END copied NBH_LiveValidator
-- BEGIN copied NBH_NativeFrontier: lean/NBH_NativeFrontier.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBH_NativeFrontier
open Aeneas Aeneas.Std Result ControlFlow WP AspisR1TerminalDecoder
open NBH_Frontier NBD_DigestInduction
attribute [local instance] Classical.propDecidable
abbrev Error := pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1

def step (a : Frontier) (i : Nat) : Nat × Option Error :=
  if h : i < 20 then
    if Canonical (a.val[i]'(by have := a.property; scalar_tac)) then (i+1,none)
    else (i,some .NonCanonicalAfterstate)
  else (i,none)

def observe (i : Usize) : ControlFlow Usize (core.result.Result Unit Error) → Nat × Option Error
  | .cont n => (n.val,none)
  | .done (.Ok _) => (i.val,none)
  | .done (.Err e) => (i.val,some e)

theorem source (a : Frontier) (i : Usize) (hi : i.val ≤ 20) :
    (do let out ← pool_v1.pair_terminal.validate_verified_afterstate_loop.body a i
        ok (observe i out)) = ok (step a i.val) := by
  have spec : pool_v1.pair_terminal.validate_verified_afterstate_loop.body a i
      ⦃ out => observe i out = step a i.val ⦄ := by
    unfold pool_v1.pair_terminal.validate_verified_afterstate_loop.body
    simp only [NBD_DigestInduction.source]
    step*
    all_goals simp_all [observe,step]
    all_goals scalar_tac
  obtain ⟨out,call,same⟩ := WP.spec_imp_exists spec
  simp only [call,bind_tc_ok,same]

#print axioms source
end NFY_NBH_NativeFrontier
-- END copied NBH_NativeFrontier
-- BEGIN copied NBH_NativeLiveFrontier: lean/NBH_NativeLiveFrontier.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBH_NativeLiveFrontier
open Aeneas Aeneas.Std Result ControlFlow WP AspisR1TerminalDecoder
open NBH_Frontier NBD_DigestInduction
attribute [local instance] Classical.propDecidable
abbrev Error := pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1

def step (a : Frontier) (i : Nat) : Nat × Option Error :=
  if h : i < 20 then
    if Canonical (a.val[i]'(by have := a.property; scalar_tac)) then (i+1,none)
    else (i,some .NonCanonicalDigest)
  else (i,none)

def observe (i : Usize) : ControlFlow Usize (core.result.Result Unit Error) → Nat × Option Error
  | .cont n => (n.val,none)
  | .done (.Ok _) => (i.val,none)
  | .done (.Err e) => (i.val,some e)

theorem source (a : Frontier) (i : Usize) (hi : i.val ≤ 20) :
    (do let out ← pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1_loop.body a i
        ok (observe i out)) = ok (step a i.val) := by
  have spec : pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1_loop.body a i
      ⦃ out => observe i out = step a i.val ⦄ := by
    unfold pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1_loop.body
    simp only [NBD_DigestInduction.source]
    step*
    all_goals simp_all [observe,step]
    all_goals scalar_tac
  obtain ⟨out,call,same⟩ := WP.spec_imp_exists spec
  simp only [call,bind_tc_ok,same]

#print axioms source
end NFY_NBH_NativeLiveFrontier
-- END copied NBH_NativeLiveFrontier

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
