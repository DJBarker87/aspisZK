import NDO_JFs_TX2_Geo10
import NDO_JFs_TX2_Geo11
import NDO_JFs_TX2_Geo12
import NDO_JFs_TX2_Geo13
import NDO_JFs_TX2_Geo14
import NDO_JFs_TX2_Geo15
import NDO_JFs_TX2_Geo16
import NDO_JFs_TX2_Geo17
import NDO_JFs_TX2_Geo18
import NDO_JFs_TX2_Geo19
import NDO_JFs_TX2_Geo20
import NDO_JFs_TX2_Geo21
import NDO_JFs_TX2_Partial
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_GeometryPoints
open Aeneas Aeneas.Std Result
open AspisR1QueryGeometryActual
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def input (i : Fin 12) (kind : Fin 3) : Usize := match i.val,kind.val with
  | 0,0 => 132355#usize
  | 0,1 => 132352#usize
  | 0,_ => 132355#usize
  | 1,0 => 218094#usize
  | 1,1 => 218092#usize
  | 1,_ => 218095#usize
  | 2,0 => 178080#usize
  | 2,1 => 178080#usize
  | 2,_ => 178083#usize
  | 3,0 => 149624#usize
  | 3,1 => 149624#usize
  | 3,_ => 149627#usize
  | 4,0 => 166165#usize
  | 4,1 => 166164#usize
  | 4,_ => 166167#usize
  | 5,0 => 42158#usize
  | 5,1 => 42156#usize
  | 5,_ => 42159#usize
  | 6,0 => 179622#usize
  | 6,1 => 179620#usize
  | 6,_ => 179623#usize
  | 7,0 => 21248#usize
  | 7,1 => 21248#usize
  | 7,_ => 21251#usize
  | 8,0 => 63860#usize
  | 8,1 => 63860#usize
  | 8,_ => 63863#usize
  | 9,0 => 55377#usize
  | 9,1 => 55376#usize
  | 9,_ => 55379#usize
  | 10,0 => 185637#usize
  | 10,1 => 185636#usize
  | 10,_ => 185639#usize
  | _,0 => 14297#usize
  | _,1 => 14296#usize
  | _,_ => 14299#usize

def value (i : Fin 12) (kind : Fin 3) : domain.Point U32 := match i.val,kind.val with
  | 0,0 => JFs_TX2_Geo10.value0
  | 0,1 => JFs_TX2_Geo10.value1
  | 0,_ => JFs_TX2_Geo10.value2
  | 1,0 => JFs_TX2_Geo11.value0
  | 1,1 => JFs_TX2_Geo11.value1
  | 1,_ => JFs_TX2_Geo11.value2
  | 2,0 => JFs_TX2_Geo12.value0
  | 2,1 => JFs_TX2_Geo12.value1
  | 2,_ => JFs_TX2_Geo12.value2
  | 3,0 => JFs_TX2_Geo13.value0
  | 3,1 => JFs_TX2_Geo13.value1
  | 3,_ => JFs_TX2_Geo13.value2
  | 4,0 => JFs_TX2_Geo14.value0
  | 4,1 => JFs_TX2_Geo14.value1
  | 4,_ => JFs_TX2_Geo14.value2
  | 5,0 => JFs_TX2_Geo15.value0
  | 5,1 => JFs_TX2_Geo15.value1
  | 5,_ => JFs_TX2_Geo15.value2
  | 6,0 => JFs_TX2_Geo16.value0
  | 6,1 => JFs_TX2_Geo16.value1
  | 6,_ => JFs_TX2_Geo16.value2
  | 7,0 => JFs_TX2_Geo17.value0
  | 7,1 => JFs_TX2_Geo17.value1
  | 7,_ => JFs_TX2_Geo17.value2
  | 8,0 => JFs_TX2_Geo18.value0
  | 8,1 => JFs_TX2_Geo18.value1
  | 8,_ => JFs_TX2_Geo18.value2
  | 9,0 => JFs_TX2_Geo19.value0
  | 9,1 => JFs_TX2_Geo19.value1
  | 9,_ => JFs_TX2_Geo19.value2
  | 10,0 => JFs_TX2_Geo20.value0
  | 10,1 => JFs_TX2_Geo20.value1
  | 10,_ => JFs_TX2_Geo20.value2
  | _,0 => JFs_TX2_Geo21.value0
  | _,1 => JFs_TX2_Geo21.value1
  | _,_ => JFs_TX2_Geo21.value2

theorem source (i : Fin 12) (kind : Fin 3) :
    fast_domain.fibre_point R17CurrentCM31Semantics.operations (input i kind)=ok (value i kind) := by
  fin_cases i
  · fin_cases kind
    · exact JFs_TX2_Geo10.source0
    · exact JFs_TX2_Geo10.source1
    · exact JFs_TX2_Geo10.source2
  · fin_cases kind
    · exact JFs_TX2_Geo11.source0
    · exact JFs_TX2_Geo11.source1
    · exact JFs_TX2_Geo11.source2
  · fin_cases kind
    · exact JFs_TX2_Geo12.source0
    · exact JFs_TX2_Geo12.source1
    · exact JFs_TX2_Geo12.source2
  · fin_cases kind
    · exact JFs_TX2_Geo13.source0
    · exact JFs_TX2_Geo13.source1
    · exact JFs_TX2_Geo13.source2
  · fin_cases kind
    · exact JFs_TX2_Geo14.source0
    · exact JFs_TX2_Geo14.source1
    · exact JFs_TX2_Geo14.source2
  · fin_cases kind
    · exact JFs_TX2_Geo15.source0
    · exact JFs_TX2_Geo15.source1
    · exact JFs_TX2_Geo15.source2
  · fin_cases kind
    · exact JFs_TX2_Geo16.source0
    · exact JFs_TX2_Geo16.source1
    · exact JFs_TX2_Geo16.source2
  · fin_cases kind
    · exact JFs_TX2_Geo17.source0
    · exact JFs_TX2_Geo17.source1
    · exact JFs_TX2_Geo17.source2
  · fin_cases kind
    · exact JFs_TX2_Geo18.source0
    · exact JFs_TX2_Geo18.source1
    · exact JFs_TX2_Geo18.source2
  · fin_cases kind
    · exact JFs_TX2_Geo19.source0
    · exact JFs_TX2_Geo19.source1
    · exact JFs_TX2_Geo19.source2
  · fin_cases kind
    · exact JFs_TX2_Geo20.source0
    · exact JFs_TX2_Geo20.source1
    · exact JFs_TX2_Geo20.source2
  · fin_cases kind
    · exact JFs_TX2_Geo21.source0
    · exact JFs_TX2_Geo21.source1
    · exact JFs_TX2_Geo21.source2

theorem input_binding (i : Fin 12) :
    (input i 0).val=(JFo_Prepared.value.queries.val[10+i.val]'(by rw [JFo_Prepared.value.queries.property];change 10+i.val<22;have:=i.isLt;omega)).val ∧
    (input i 1).val=(input i 0).val/4*4 ∧ (input i 2).val=(input i 1).val+3 := by
  fin_cases i <;> exact ⟨rfl,rfl,rfl⟩

theorem regular (i : Fin 12) (kind : Fin 3) :
    (value i kind).x.val<2147483647 ∧ (value i kind).y.val<2147483647 ∧
    (value i kind).x≠0#u32 ∧ (value i kind).y≠0#u32 := by
  fin_cases i <;> fin_cases kind <;> decide

theorem on_saved (saved : alloc.vec.Vec U8) (same : saved.val=JFx_NativeBytes.checkpoint.val)
    {Hash : Type} (H : Bytes → State) (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (realizes : JFn_HashBoundary.Realizes H) (seed : Port3_NativeQueryBody.Ops) :
    Port4A_ReaderInstall.reader true (JFn_HashBoundary.dictionary H D)
      (⟨saved.val,saved.property⟩ : Slice U8) JFx_NativeBytes.proof JFx_NativeBytes.publicInput .S2 hash=
      ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) ∧
    JFs_TX2_Partial.Calls seed ∧
    (∀ i : Fin 12, ∀ kind : Fin 3,
      fast_domain.fibre_point R17CurrentCM31Semantics.operations (input i kind)=ok (value i kind)) := by
  exact ⟨JFn_Resume.on_saved saved same H D hash realizes,JFs_TX2_Partial.calls seed,source⟩

/-- Joint consistency of the reader, installed dots and these real geometry
point calls under the inherited finite model extension, not SHA256. -/
theorem inhabited {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (background : Bytes → State) (seed : Port3_NativeQueryBody.Ops) :
    ∃ H : Bytes → State, JFn_HashBoundary.Realizes H ∧
      Port4A_ReaderInstall.reader true (JFn_HashBoundary.dictionary H D)
        JFx_NativeBytes.checkpoint JFx_NativeBytes.proof JFx_NativeBytes.publicInput .S2 hash=
        ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) ∧
      JFs_TX2_Partial.Calls seed ∧
      (∀ i : Fin 12, ∀ kind : Fin 3,
        fast_domain.fibre_point R17CurrentCM31Semantics.operations (input i kind)=ok (value i kind)) := by
  obtain ⟨H,realizes,reader,calls⟩ := JFs_TX2_Partial.inhabited D hash background seed
  exact ⟨H,realizes,reader,calls,source⟩

#print axioms source
#print axioms input_binding
#print axioms regular
#print axioms on_saved
#print axioms inhabited
end AspisR1.JFs_TX2_GeometryPoints
end
