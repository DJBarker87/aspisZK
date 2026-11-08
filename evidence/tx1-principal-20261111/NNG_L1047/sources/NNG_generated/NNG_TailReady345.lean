import NNG_FirstArgs345
import NNG_ChildAssociation345
import NNG_BoundsAssociation345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_TailReady345
open Aeneas Aeneas.Std Result NMT_345 NMT_CallTree NNG_Observed136

def guarded {W : Type} (s : ProofData W) (tag split : U8) (env : RSL.Env) :=
 if !decide ((NNG_Windows345.window s.proofData 0 688).val=s.candidate.val) then
  NNG_Pure345.silent (.error RSL.ProgramError.invalidAccountData) else
 if tag != 2#u8 then NNG_Pure345.silent (.error RSL.ProgramError.invalidAccountData) else
 NNG_Obs345.tryObs
  (NNG_Producer328.producer (NNG_ChildSource345.args (semanticValue s.statement) s.publicData
   (NNG_Windows345.window s.proofData 688 58295) (UScalar.cast .Usize split)) env)
  (NNG_Phases345.stepReturn (LIB_Carriers.bytes s.checkpointData).length)

theorem source {W : Type} (s : ProofData W) (env : RSL.Env)
 (length : s.proofData.val.length=58295) (route : s.data.val.length=2) :
 observation NNG_ChildSource345.port (NNG_Events345.events env)
 (NNG_TreeTail345.bounds (NNG_Calls345.calls env) s)=
 guarded s (s.proofData.val[696]'(by omega)) (s.data.val[1]'(by omega)) env := by
 rw [NNG_BoundsAssociation345.source]
 have nativeLength : Slice.len s.proofData=58295#usize := UScalar.eq_of_val_eq length
 unfold NNG_TreeTail345.tail
 rw [nativeLength]
 simp only [bne_self_eq_false,Bool.false_eq_true,if_false]
 rw [NNG_Windows345.prefix_range s.proofData 688#usize (by scalar_tac)]
 change observation _ _ (do
  let mismatch ← (liftM (NNG_Calls345.neArray core.cmp.PartialEqU8
    (NNG_Windows345.window s.proofData 0 688) s.candidate) : Code _)
  if mismatch then (pure (.Err .InvalidAccountData) : Code Ret) else _) = _
 rw [NNG_Compare345.unequal]
 unfold guarded
 split
 · rfl
 · change observation _ _ (do
    let tag ← (liftM (Slice.index_usize s.proofData 696#usize) : Code _)
    let expected ← (liftM ((NNG_Calls345.calls env).c3 NMT_stage1_owned.aspis_r1_cost_probe.transport.Variant.S2) : Code _)
    if tag != expected then (pure (.Err .InvalidAccountData) : Code Ret) else _) = _
   have tagRead := NNG_Windows345.index s.proofData 696#usize (by scalar_tac)
   rw [tagRead]
   change observation _ _ (if (s.proofData.val[696]'(by omega)) != 2#u8
      then (pure (.Err .InvalidAccountData) : Code Ret) else _) = _
   split
   · rfl
   · rw [NNG_Windows345.range s.proofData 688#usize 58295#usize (by scalar_tac)]
     rw [NNG_Windows345.index s.data 1#usize (by scalar_tac)]
     exact NNG_ChildAssociation345.source (semanticValue s.statement) s.publicData
       (NNG_Windows345.window s.proofData 688 58295) s.checkpointData
       (UScalar.cast .Usize (s.data.val[1]'(by omega))) env (NNG_SplitByte345.bound _)
#print axioms source
end AspisR1.NNG_TailReady345
