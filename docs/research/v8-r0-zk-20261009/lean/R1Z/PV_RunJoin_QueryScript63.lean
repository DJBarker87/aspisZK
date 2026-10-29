import R1Z.PV_RunJoin_ByteScript63
import R1Z.PV_RunJoin_OpeningPrefix63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryScript63
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_ByteScript63 (Code)
open PV_RunJoin_WeightInstalled46
abbrev W := aspis_core.field.wide_exact.WideExact
variable [ExternalTypes] [ExternalFuns]

def head (cc1 cc2 : host_commitment.Commitment) (queries : Array U32 22#usize) (i : Usize) :
    Result (aspis_core.r0.domain.FibreIndex × aspis_core.r0.wire.FibreOpening) := do
  let q ← Array.index_usize queries i
  let r ← aspis_core.r0.domain.FibreIndex.new (UScalar.cast .Usize q)
  let u ← unwrapSlice r
  let zero ← aspis_core.field.wide_exact.WideExact.ZERO
  let opening ← host_commitment.Commitment.fill_opening cc1 u
    ⟨Array.repeat 4#usize (Array.repeat 29#usize zero),
      Array.repeat 2#usize (Array.repeat 6#usize (Array.repeat 7#usize (Array.repeat 32#usize 0#u8)))⟩
  let opening ← host_commitment.Commitment.fill_opening cc2 u opening
  ok (u,opening)

def openingSlice (opening : aspis_core.r0.wire.FibreOpening) : Slice U8 :=
  ⟨PV_RunJoin_OpeningPrefix63.payload opening,by
    rw [PV_RunJoin_OpeningPrefix63.length]; scalar_tac⟩

def tail (cc1 cc2 : host_commitment.Commitment) (u : aspis_core.r0.domain.FibreIndex)
    (folded : Slice W) (salts : host_commitment.PrivateSalts) : Code :=
  Code.read (host_commitment.Commitment.opening_salt cc1 u) fun first =>
  Code.read (core.option.Option.unwrap first) fun salt1 =>
  Code.append (Array.to_slice salt1) $
  Code.read (host_commitment.Commitment.opening_salt cc2 u) fun second =>
  Code.read (core.option.Option.unwrap second) fun salt2 =>
  Code.append (Array.to_slice salt2) $
  Code.read (aspis_core.r0.domain.FibreIndex.get u) fun index =>
  Code.read (index / 4#usize) fun quarter =>
  let begin1 := Usize.wrapping_mul 4#usize quarter
  let end1 := Usize.wrapping_add begin1 4#usize
  Code.read (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice W)
    folded ⟨begin1,end1⟩) fun values =>
  Code.read (prover.encoded_slice values) fun encoded =>
  Code.append (alloc.vec.Vec.deref encoded) $
  Code.read (index / 4#usize) fun quarter =>
  Code.read (host_commitment.PrivateSalts.get salts quarter) fun salt =>
  Code.append (Array.to_slice salt) Code.done

def script (cc1 cc2 : host_commitment.Commitment) (queries : Array U32 22#usize)
    (folded : Slice W) (salts : host_commitment.PrivateSalts) (i : Usize) : Code :=
  Code.read (head cc1 cc2 queries i) fun pair =>
    Code.append (openingSlice pair.2) (tail cc1 cc2 pair.1 folded salts)

#print axioms head
#print axioms openingSlice
#print axioms tail
#print axioms script
end R1Z.PV_RunJoin_QueryScript63
