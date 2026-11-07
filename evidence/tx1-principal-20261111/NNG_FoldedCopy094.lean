import NNG_Producer094
import MultiproofConeSlices
import NNG_Root32
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_FoldedCopy094
open Aeneas Aeneas.Std Result NMT_tx1 NMT_CallTree NNG_Observed136

def bytes (proof : Slice U8) := MultiproofConeSlices.sub proof 7751#usize 7783#usize

theorem width (proof : Slice U8) (h : proof.val.length=57607) : (bytes proof).val.length=32 :=
 MultiproofConeSlices.sub_length proof _ _ (by decide) (by rw [h];decide)

def root (proof : Slice U8) (h : proof.val.length=57607) : Array U8 32#usize := ⟨(bytes proof).val,width proof h⟩

theorem exact_bytes (proof : Slice U8) (h : proof.val.length=57607) :
 (root proof h).val=(proof.val.drop 7751).take 32 := rfl
#print axioms exact_bytes

theorem reference (proof : Slice U8) (h : proof.val.length=57607) :
 RSL.TX1_136.toB32 (RSL.slice (LIB_Carriers.bytes proof) RSL.OFF_FOLDED_ROOT RSL.OFF_ROUND1)=
 some (LIB_Carriers.b32 (root proof h)) := by
 have same : RSL.slice (LIB_Carriers.bytes proof) RSL.OFF_FOLDED_ROOT RSL.OFF_ROUND1=
  LIB_Carriers.bytes (bytes proof) := by
  unfold RSL.slice LIB_Carriers.bytes NMS_R2N_RSLScalars.bytes bytes MultiproofConeSlices.sub
  simp only [List.map_take,List.map_drop]
  rfl
 rw [same]
 unfold RSL.TX1_136.toB32
 have len : (LIB_Carriers.bytes (bytes proof)).length=32 := by
  rw [NMS_R2N_RSLScalars.bytes_length]
  exact width proof h
 rw [dif_pos len]
 rfl
#print axioms reference

theorem source (env : RSL.Env) (s : NNG_Context094.Parent Unit)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (p : verifier.Prepared) (a : verifier.Accumulator)
 (h : s.proof.val.length=57607) :
 observation NNG_Producer094.port (NNG_Events094.events env)
  (NNG_Tree094.f_i (NNG_InstalledCalls094.calls env) s g p a)=
 observation NNG_Producer094.port (NNG_Events094.events env)
  (NNG_Tree094.f_r5 (NNG_InstalledCalls094.calls env) s g p a (root s.proof h)) := by
 have range := MultiproofConeSlices.range_total s.proof 7751#usize 7783#usize (by decide) (by rw [h];decide)
 have converted : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 (bytes s.proof)=
  ok (.Ok (root s.proof h)) := by
  unfold core.array.TryFromArrayCopySlice.try_from
  have len : (bytes s.proof).length=(32#usize).val := width s.proof h
  rw [dif_pos len]
  rfl
 unfold NNG_Tree094.f_i NNG_Tree094.f_i1 NNG_Tree094.f_s
 change observation _ _ (Code.plain (ok 7751#usize) (fun i=>Code.plain (ok 7783#usize) (fun j=>
  Code.plain (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) s.proof {start:=i,«end»:=j})
   (fun part=>NNG_Tree094.f_r4 (NNG_InstalledCalls094.calls env) s g p a part))))=_
 change observation _ _ (Code.plain
  (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) s.proof {start:=7751#usize,«end»:=7783#usize})
  (fun part=>NNG_Tree094.f_r4 (NNG_InstalledCalls094.calls env) s g p a part))=_
 rw [range]
 change observation _ _ (NNG_Tree094.f_r4 (NNG_InstalledCalls094.calls env) s g p a (bytes s.proof))=_
 unfold NNG_Tree094.f_r4
 rw [converted]
 rfl
#print axioms source
end AspisR1.NNG_FoldedCopy094
