import R1Z.PV_CBL_PadContentSource
import R1Z.PV_CBL_PaddingCount
import R1Z.PV_DL_CompressionTrace
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
