import NKI_InitialPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_TermAmount
open Aeneas Aeneas.Std Result FIq_Native
open NKI_InitialPrefix (Public)
open pool_v1.pair_forest_semantic_terminal

def invalid : Option U32 → Bool
 | none=>false
 | some a=>decide (a=0#u32 ∨ 1073741824≤a.val)

def run (p : Public) : Result (Option U32 × Bool) :=
 match p.withdrawal_amount with
 | none=>ok (none,false)
 | some amount=>do
   let b←if amount=0#u32 then ok true else do
     let i←1#u32 <<< 30#u32
     ok (decide (amount>=i))
   ok (p.withdrawal_amount,b)

/--237 amount precheck's exact full Result. It retains the original option
and permits both arbitrary rejected cases instead of an accepted-input premise. -/
theorem source (p : Public) : run p=ok (p.withdrawal_amount,invalid p.withdrawal_amount) := by
 cases h : p.withdrawal_amount with
 | none=>simp only [run,h,invalid]
 | some a=>
   simp only [run,h,invalid]
   by_cases zero : a=0#u32
   · simp only [zero,ite_true,bind_tc_ok,true_or,decide_true]
   · have shift : (1#u32 <<< 30#u32 : Result U32)=ok 1073741824#u32 := by rfl
     simp only [shift,zero,false_or,ite_false,bind_tc_ok]
     rfl

/-- The scalar261 withdrawal argument domain is established by237's own
precheck at its SAME actual amount. No child success is assumed. -/
theorem canonical (p : Public) (good : invalid p.withdrawal_amount=false) :
 (core.option.Option.unwrap_or p.withdrawal_amount 0#u32).val<2147483647 := by
 cases h : p.withdrawal_amount with
 | none=>simp only [h,core.option.Option.unwrap_or];decide
 | some a=>
   have low : a.val<1073741824 := by
    have bad : ¬(a=0#u32 ∨ 1073741824≤a.val) := by
     simpa only [h,invalid,decide_eq_false_iff_not] using good
    omega
   simpa only [h,core.option.Option.unwrap_or] using (show a.val<2147483647 by omega)

/-- Complete invalid amount arm:237 returns exactly its public error before
validation, gathers,308,261,218, or any Horner operation is entered. -/
theorem rejected (p : Public) (claims : Array field.QM31 84#usize) (point : Array field.QM31 10#usize)
 (lambda chi theta : field.QM31) (bad : invalid p.withdrawal_amount=true) :
 composition_parts p claims point lambda chi theta=ok (.Err .InvalidPublicAmount) := by
 cases h : p.withdrawal_amount with
 | none=>simp only [h,invalid] at bad;cases bad
 | some a=>
   unfold composition_parts
   rw [h]
   by_cases zero : a=0#u32
   · simp only [zero,ite_true,bind_tc_ok,Aeneas.Std.uncurry]
   · have lower : 1073741824≤a.val := by
      have cases' : a=0#u32 ∨ 1073741824≤a.val := of_decide_eq_true (by simpa only [h,invalid] using bad)
      exact cases'.resolve_left zero
     have ge : a>=1073741824#u32 := lower
     have shift : (1#u32 <<< 30#u32 : Result U32)=ok 1073741824#u32 := by rfl
     simp only [if_neg zero,shift,bind_tc_ok,Aeneas.Std.uncurry,ge,decide_true,ite_true]

#print axioms source
#print axioms canonical
#print axioms rejected
end AspisR1.NLH_TermAmount
end
