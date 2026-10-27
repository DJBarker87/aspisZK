from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2]
qs=[93499,147529,216823,245899,209371,192317,65593,183859,193093,159813]
for k in range(3):
 name=f'JGp_Keys{k}';ks=[256*(q//4 if k==2 else q)+i for i,q in enumerate(qs)]+[0]*6
 s=f'''import JFq_Queries
import Op5T_Concrete
set_option autoImplicit false
noncomputable section
namespace AspisR1.{name}
open Aeneas Aeneas.Std Result

def value : Array U64 16#usize := Array.make 16#usize [{','.join(str(n)+'#u64' for n in ks)}]

theorem content : Port4B_KeyInstall.keyArray JFq_Queries.value 0 {k}=value := by
  apply Subtype.ext
  rfl
#print axioms content

theorem source : Port4B_KeyInstall.build JFq_Queries.value 0#usize 10#usize {k}#usize=ok value := by
  unfold Port4B_KeyInstall.build
  rw [if_pos rfl]
  have good : (10#usize).val=(OraclePortSelectedDraft.batchPositions 0).length ∧
      (0#usize=0#usize ∨ 0#usize=10#usize) ∧ ({k}#usize).val<3 := ⟨rfl,Or.inl rfl,by decide⟩
  erw [dif_pos good]
  exact congrArg Result.ok content
#print axioms source
end AspisR1.{name}
end
'''
 f=R/f'lean/{name}.lean'
 if '--check' in sys.argv:assert f.read_text()==s,f
 else:f.write_text(s)
for k,(off,n) in enumerate([(28359,4672),(33031,4672),(37703,4096)]):
 name=f'JGp_Slot{k}'
 s=f'''import Port4B_SlotInstall
import JFw_Range
set_option autoImplicit false
noncomputable section
namespace AspisR1.{name}
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof JFx_NativeBytes.proofBytes JFw_Frames.window

def value : Slice U8 := JFw_Frames.window {off} {n}
theorem length : value.length={n} := JFw_Frames.window_length {off} {n} (by decide)
#print axioms length

theorem source : Port4B_SlotInstall.nodeSlot JFx_NativeBytes.proof {k}#usize=ok value := by
  unfold Port4B_SlotInstall.nodeSlot
  erw [dif_pos (show ({k}#usize).val<6 by decide)]
  have start : Port4B_SlotInstall.offset ({k}#usize).val (by decide)={off}#usize := by
    apply UScalar.eq_of_val_eq
    rfl
  have finish : Port4B_SlotInstall.offset (({k}#usize).val+1) (by decide)={off+n}#usize := by
    apply UScalar.eq_of_val_eq
    rfl
  erw [start,finish]
  have read := JFw_Range.read {off}#usize {off+n}#usize (by decide) (by decide)
  exact read
#print axioms source
end AspisR1.{name}
end
'''
 f=R/f'lean/{name}.lean'
 if '--check' in sys.argv:assert f.read_text()==s,f
 else:f.write_text(s)
print('checked' if '--check' in sys.argv else 'generated','batch0 keys and physical slots')
