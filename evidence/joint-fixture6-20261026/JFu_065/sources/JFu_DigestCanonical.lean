import JFu_DigestDecode
set_option autoImplicit false
namespace AspisR1.JFu_DigestCanonical
open Aeneas Aeneas.Std Result WP
open AspisR1TerminalDecoder

def Canonical (q : Array U32 8#usize) : Prop :=
  ∀ i : Fin 8,(q.val[i.val]'(by simpa only [q.property,show (8#usize).val=8 from rfl] using i.isLt)).val<2147483647

@[local step] theorem word (arr : Array U8 4#usize) :
    aspis_core.field.M31.from_le_bytes arr
      ⦃ out => ∀ v,out=some v → v.val<2147483647 ⦄ := by
  unfold aspis_core.field.M31.from_le_bytes
  step*
  all_goals intro v same
  all_goals simp_all [aspis_core.field.P]
  all_goals scalar_tac

@[local step] theorem option {T E : Type} (o : Option T) (e : E) :
    core.option.Option.ok_or o e ⦃ out => ∀ v,out=.Ok v → o=some v ⦄ := by
  apply exists_imp_spec
  cases o <;> refine ⟨_,rfl,?_⟩ <;> simp

theorem source (arr : Array U8 32#usize) (out : Array U32 8#usize)
    (accepted : atomic_statement.decode_digest_canonical arr=ok (.Ok out)) : Canonical out := by
  have spec : atomic_statement.decode_digest_canonical arr
      ⦃ result => ∀ q,result=.Ok q → Canonical q ⦄ := by
    unfold atomic_statement.decode_digest_canonical
    step*
    all_goals intro q eq
    all_goals cases eq
    all_goals (have rv0 : r=.Ok val := by cases r <;> simp_all [core.result.Result.Insts.CoreOpsTry.branch])
    all_goals have hv0:=o_post _ (r_post _ rv0)
    all_goals (have rv1 : r1=.Ok val1 := by cases r1 <;> simp_all [core.result.Result.Insts.CoreOpsTry.branch])
    all_goals have hv1:=o1_post _ (r1_post _ rv1)
    all_goals (have rv2 : r2=.Ok val2 := by cases r2 <;> simp_all [core.result.Result.Insts.CoreOpsTry.branch])
    all_goals have hv2:=o2_post _ (r2_post _ rv2)
    all_goals (have rv3 : r3=.Ok val3 := by cases r3 <;> simp_all [core.result.Result.Insts.CoreOpsTry.branch])
    all_goals have hv3:=o3_post _ (r3_post _ rv3)
    all_goals (have rv4 : r4=.Ok val4 := by cases r4 <;> simp_all [core.result.Result.Insts.CoreOpsTry.branch])
    all_goals have hv4:=o4_post _ (r4_post _ rv4)
    all_goals (have rv5 : r5=.Ok val5 := by cases r5 <;> simp_all [core.result.Result.Insts.CoreOpsTry.branch])
    all_goals have hv5:=o5_post _ (r5_post _ rv5)
    all_goals (have rv6 : r6=.Ok val6 := by cases r6 <;> simp_all [core.result.Result.Insts.CoreOpsTry.branch])
    all_goals have hv6:=o6_post _ (r6_post _ rv6)
    all_goals (have rv7 : r7=.Ok val7 := by cases r7 <;> simp_all [core.result.Result.Insts.CoreOpsTry.branch])
    all_goals have hv7:=o7_post _ (r7_post _ rv7)
    all_goals unfold Canonical
    all_goals intro j
    all_goals fin_cases j <;> simp_all [Array.make]
  obtain ⟨result,call,post⟩:=WP.spec_imp_exists spec
  have same : result=.Ok out := Result.ok.inj (call.symm.trans accepted)
  exact post out same

#print axioms word
#print axioms option
#print axioms source
end AspisR1.JFu_DigestCanonical
