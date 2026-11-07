import NMB_Stage1Parent
import NMB_Stage1Result
set_option autoImplicit false
noncomputable section
namespace NMB_Stage1Admitted
open Aeneas Aeneas.Std Result AspisR1 NMB_Stage1Source NMB_Stage1Parent
theorem body (x : NMB_Input.Input) (ops : AdapterRw.Ops) (p : Key) (d : Slice U8)
 (a0 a1 a2 : Result Unit) (tx1 : NLQ_Route.Tx1 d) :
 (NMB_Stage1Parent.G x ops p d 3 a0 a1 a2).result=
 (NMB_Stage1Source.G x ops p d a0 a1 a2).result ∧
 (NMB_Stage1Parent.G x ops p d 3 a0 a1 a2).post=
 (NMB_Stage1Source.G x ops p d a0 a1 a2).post := by
 rcases tx1 with ten | eleven
 · simp [NMB_Stage1Parent.G,ten,prepend,count]
 · by_cases ten : d.val=[3#u8,10#u8] <;>
    simp [NMB_Stage1Parent.G,ten,eleven,prepend,count]
/-- Complete Result on the normal allocator branch, with the actual owned
child split internally. Retained Ops is source-only, never a root premise. -/
theorem result (x : NMB_Input.Input) (ops : AdapterRw.Ops) (p : Key) (d : Slice U8)
 (tx1 : NLQ_Route.Tx1 d) :
 (NMB_Stage1Parent.G x ops p d 3 (.ok ()) (.ok ()) (.ok ())).result=
 (do let child ← AdapterRw.r1_pool_adapter.owned.stage1_owned ops p (NMB_ThreeSnapshots.first x) d
     match child with
     | .Ok _ => ok (.Ok ())
     | .Err error => ok (.Err error)) :=
 (body x ops p d _ _ _ tx1).1.trans (NMB_Stage1Result.result x ops p d)
#print body
#print result
#print axioms body
#print axioms result
end NMB_Stage1Admitted
