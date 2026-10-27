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
    all_goals unfold Canonical
    all_goals intro j
    all_goals have h:=j.isLt
    all_goals interval_cases hj : j.val <;> simp_all [Array.make,
      core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  obtain ⟨result,call,post⟩:=WP.spec_imp_exists spec
  have same : result=.Ok out := Result.ok.inj (call.symm.trans accepted)
  exact post out same

#print axioms word
#print axioms option
#print axioms source
end AspisR1.JFu_DigestCanonical
