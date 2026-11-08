import NNG_Primitives345
import NNG_CheckpointGraph345
import NNG_DecoderEffects345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_PrefixEquations345
open Aeneas Aeneas.Std Result NMT_345 RSL

theorem distinct {W : Type} (s : Selected W) (env : Env) :
 NNG_Observe345.observe id ((NNG_Calls345.calls env).c15 (selectedArray s))=
 NNG_Pure345.silent (requireDistinct [account s.proofAccount,account s.publicAccount,account s.checkpointAccount]) :=
 NNG_Primitives345.distinct s env
#print axioms distinct

theorem readonly (a : Account) (env : Env) :
 NNG_Observe345.observe id ((NNG_Calls345.calls env).c13 a)=
 NNG_Pure345.silent (readonlyBuffer (account a)) := NNG_Primitives345.readonly a env
#print axioms readonly

theorem zero (b : Slice U8) (env : Env) :
 NNG_Observe345.observe id ((NNG_Calls345.calls env).c16 b)=
 NNG_Pure345.silent (requireZero (LIB_Carriers.bytes b)) := by
 rw [← NNG_DecoderGraph345.bytes]
 exact NNG_Primitives345.zero b env
#print axioms zero

theorem clone_true (e : PE) : NNG_Observe345.clone true e=ok e := by
 simp only [NNG_Observe345.clone,Bool.not_true,Bool.and_false,Bool.false_eq_true,if_false]
#print axioms clone_true

theorem checkpoint_ops : NNG_LengthNative345.ops true=NGL_CheckpointModel.install baseOps := by
 unfold NNG_LengthNative345.ops
 simp only [clone_true,mapOuter,to_fromPE]
 rfl
#print axioms checkpoint_ops

theorem checkpoint (a : Account) (program : Key) (env : Env) :
 NNG_Observe345.observe id ((NNG_Calls345.calls env).c14 a program true)=
 NNG_Phases345.checkpointObservation true (account a) (key program) true := by
 rw [← NNG_CheckpointGraph345.native_eq true a program true]
 unfold NNG_CheckpointGraph345.run NNG_EquationNative345.native
 rw [checkpoint_ops]
 rfl
#print axioms checkpoint

theorem data (a : Account) (env : Env) :
 NNG_Observe345.observe (fun b : Slice U8=>LIB_Carriers.bytes b)
 (NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data (NNG_Calls345.calls env).c10 a)=
 NNG_Pure345.cloned true (account a).bytes := by
 rw [← NNG_Observe345.data true a]
 have clone : NNG_Observe345.clone true=(fun e : PE=>ok e) := funext clone_true
 unfold NNG_Observe345.run
 rw [clone]
 congr 1
 funext b
 exact NNG_DecoderGraph345.bytes b |>.symm
#print axioms data

theorem decoder (b : Slice U8) :
 NNG_DecoderEffects345.run true true b=NNG_Observe345.observe id (decodeCall b) := by
 unfold NNG_DecoderEffects345.run
 cases LIBC_S1.reaches (LIB_Carriers.bytes b) <;>
  cases decodeCall b with
  | fail e=>rfl
  | div=>rfl
  | ok r=>cases r <;> rfl
#print axioms decoder
end AspisR1.NNG_PrefixEquations345
