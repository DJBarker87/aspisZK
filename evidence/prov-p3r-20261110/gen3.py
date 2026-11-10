src=open('PCVS_E002_emitted/raw/PCVS_ckpt_small/Types.lean').read()
ty=src[src.index('namespace PCVS_ckpt_small'):].replace('namespace PCVS_ckpt_small','namespace PCVS_Fresh2').replace('end PCVS_ckpt_small','')
fs=open('PCVS_E002_emitted/raw/PCVS_ckpt_small/Funs.lean').read()
fb=fs[fs.index('namespace PCVS_ckpt_small'):].replace('namespace PCVS_ckpt_small','').replace('end PCVS_ckpt_small','end PCVS_Fresh2')
head='''-- PCVS_ item (2) helpers: frozen 4bb3b3f checkpoint_size / final_len / tag / folds (PCVS_E002, ON) against the deployed CheckpointBytes4Ops values (yDep), and QM31::ZERO (PCVS_E001).
import Aeneas
import PRVEq_WideBind_s2
import PRVEq_Tx2Deployed_q5
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
set_option autoImplicit false
noncomputable section
'''
mid='''
namespace PCVS_Ckpt
open AspisR1 AspisR1.CheckpointBytes4Ops

def toF : AspisR1Stage2.transport.Variant → PCVS_Fresh2.transport.Variant
  | .S1 => .S1 | .S2 => .S2 | .D => .D

theorem tag_eq (v : AspisR1Stage2.transport.Variant) : PCVS_Fresh2.transport.Variant.tag (toF v) = tag v := by
  cases v <;> rfl

theorem folds_s1 : PCVS_Fresh2.transport.Variant.folds .S1 = ok 1#usize := by
  unfold PCVS_Fresh2.transport.Variant.folds PCVS_Fresh2.transport.Variant.Insts.CoreCmpPartialEqVariant.eq
  simp

theorem addlit (a b c : Std.Usize) (h : a.val + b.val = c.val) (hc : c.val < 4294967296) :
    (a + b : Result Std.Usize) = ok c := by
  have hmax : a.val + b.val ≤ Std.Usize.max := by scalar_tac
  obtain ⟨z, hz, hv⟩ := Aeneas.Std.WP.spec_imp_exists (Usize.add_spec (x := a) (y := b) hmax)
  rw [hz]; congr 1; apply UScalar.eq_of_val_eq; omega

theorem mullit (a b c : Std.Usize) (h : a.val * b.val = c.val) (hc : c.val < 4294967296) :
    (a * b : Result Std.Usize) = ok c := by
  have hmax : a.val * b.val ≤ Std.Usize.max := by scalar_tac
  obtain ⟨z, hz, hv⟩ := Aeneas.Std.WP.spec_imp_exists (Usize.mul_spec (x := a) (y := b) hmax)
  rw [hz]; congr 1; apply UScalar.eq_of_val_eq; omega

theorem shrlit (x i c : Std.Usize) (hi : i.val < 32) (hc : x.val >>> i.val = c.val) :
    (x >>> i : Result Std.Usize) = ok c := by
  have hb : i.val < System.Platform.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> omega
  obtain ⟨z, hz, hv⟩ := Aeneas.Std.WP.spec_imp_exists (Usize.ShiftRight_spec x i hb)
  rw [hz]; congr 1; apply UScalar.eq_of_val_eq; omega

theorem disc_s1 : (PCVS_Fresh2.transport.Variant.S1).read_discriminant.val = 0 := by
  first | (unfold PCVS_Fresh2.transport.Variant.read_discriminant; scalar_tac) | (simp [PCVS_Fresh2.transport.Variant.read_discriminant]; scalar_tac) | (simp [PCVS_Fresh2.transport.Variant.read_discriminant]; done) | (unfold PCVS_Fresh2.transport.Variant.read_discriminant; simp; done)
theorem disc_s2 : (PCVS_Fresh2.transport.Variant.S2).read_discriminant.val = 1 := by
  first | (unfold PCVS_Fresh2.transport.Variant.read_discriminant; scalar_tac) | (simp [PCVS_Fresh2.transport.Variant.read_discriminant]; scalar_tac) | (simp [PCVS_Fresh2.transport.Variant.read_discriminant]; done) | (unfold PCVS_Fresh2.transport.Variant.read_discriminant; simp; done)
theorem disc_d : (PCVS_Fresh2.transport.Variant.D).read_discriminant.val = 2 := by
  first | (unfold PCVS_Fresh2.transport.Variant.read_discriminant; scalar_tac) | (simp [PCVS_Fresh2.transport.Variant.read_discriminant]; scalar_tac) | (simp [PCVS_Fresh2.transport.Variant.read_discriminant]; done) | (unfold PCVS_Fresh2.transport.Variant.read_discriminant; simp; done)

theorem folds_s2 : PCVS_Fresh2.transport.Variant.folds .S2 = ok 2#usize := by
  unfold PCVS_Fresh2.transport.Variant.folds PCVS_Fresh2.transport.Variant.Insts.CoreCmpPartialEqVariant.eq
  simp [disc_s1, disc_s2]

theorem folds_d : PCVS_Fresh2.transport.Variant.folds .D = ok 2#usize := by
  unfold PCVS_Fresh2.transport.Variant.folds PCVS_Fresh2.transport.Variant.Insts.CoreCmpPartialEqVariant.eq
  simp [disc_s1, disc_d]

theorem final_len_eq (v : AspisR1Stage2.transport.Variant) : PCVS_Fresh2.transport.Variant.final_len (toF v) = finalLen v := by
  have h1024 : (1024#usize).val = 1024 := by scalar_tac
  have h256 : (256#usize).val = 256 := by scalar_tac
  have h64 : (64#usize).val = 64 := by scalar_tac
  have h2 : (2#usize).val = 2 := by scalar_tac
  have h4 : (4#usize).val = 4 := by scalar_tac
  cases v
  · unfold PCVS_Fresh2.transport.Variant.final_len toF
    rw [folds_s1]; simp only [bind_tc_ok]
    rw [mullit 2#usize 1#usize 2#usize (by scalar_tac) (by scalar_tac)]
    simp only [bind_tc_ok]
    rw [shrlit 1024#usize 2#usize 256#usize (by scalar_tac) (by rw [Nat.shiftRight_eq_div_pow, h1024, h2, h256])]
    rfl
  · unfold PCVS_Fresh2.transport.Variant.final_len toF
    rw [folds_s2]; simp only [bind_tc_ok]
    rw [mullit 2#usize 2#usize 4#usize (by scalar_tac) (by scalar_tac)]
    simp only [bind_tc_ok]
    rw [shrlit 1024#usize 4#usize 64#usize (by scalar_tac) (by rw [Nat.shiftRight_eq_div_pow, h1024, h4, h64])]
    rfl
  · unfold PCVS_Fresh2.transport.Variant.final_len toF
    rw [folds_d]; simp only [bind_tc_ok]
    rw [mullit 2#usize 2#usize 4#usize (by scalar_tac) (by scalar_tac)]
    simp only [bind_tc_ok]
    rw [shrlit 1024#usize 4#usize 64#usize (by scalar_tac) (by rw [Nat.shiftRight_eq_div_pow, h1024, h4, h64])]
    rfl

theorem fixed_eq : PCVS_Fresh2.verifier.CHECKPOINT_FIXED = ok 744#usize := by
  unfold PCVS_Fresh2.verifier.CHECKPOINT_FIXED
  rw [mullit 32#usize 3#usize 96#usize (by scalar_tac) (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [addlit 16#usize 96#usize 112#usize (by scalar_tac) (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [addlit 112#usize 64#usize 176#usize (by scalar_tac) (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [mullit 32#usize 4#usize 128#usize (by scalar_tac) (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [addlit 176#usize 128#usize 304#usize (by scalar_tac) (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [addlit 304#usize 16#usize 320#usize (by scalar_tac) (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [addlit 320#usize 88#usize 408#usize (by scalar_tac) (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [addlit 408#usize 160#usize 568#usize (by scalar_tac) (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [addlit 568#usize 64#usize 632#usize (by scalar_tac) (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [mullit 32#usize 2#usize 64#usize (by scalar_tac) (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [addlit 632#usize 64#usize 696#usize (by scalar_tac) (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [addlit 696#usize 16#usize 712#usize (by scalar_tac) (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [addlit 712#usize 32#usize 744#usize (by scalar_tac) (by scalar_tac)]

theorem checkpoint_size_eq (v : AspisR1Stage2.transport.Variant) : PCVS_Fresh2.verifier.checkpoint_size (toF v) = checkpointSize v := by
  unfold PCVS_Fresh2.verifier.checkpoint_size checkpointSize
  rw [final_len_eq, fixed_eq]
  simp only [bind_tc_ok]

theorem zeroK_eq (reserved : Bool) :
    (ops reserved).zeroK = ok ⟨⟨PCVS_Fresh.field.QM31.ZERO.c0.a, PCVS_Fresh.field.QM31.ZERO.c0.b⟩, ⟨PCVS_Fresh.field.QM31.ZERO.c1.a, PCVS_Fresh.field.QM31.ZERO.c1.b⟩⟩ := by
  with_unfolding_all rfl
end PCVS_Ckpt
#print PCVS_Fresh2.transport.Variant.read_discriminant
#print axioms PCVS_Ckpt.tag_eq
#print axioms PCVS_Ckpt.final_len_eq
#print axioms PCVS_Ckpt.fixed_eq
#print axioms PCVS_Ckpt.checkpoint_size_eq
#print axioms PCVS_Ckpt.zeroK_eq
'''
open('PRVEq_CkptSmall_s4.lean','w').write(head+ty+fb+mid)
