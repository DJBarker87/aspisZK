import PV_RJ4IDB_TraceBind
/-! The deployed normal suffix's order, with complete leaf executions as inputs.
No leaf I/O or time value is made successful, silent, or public by definition. -/
set_option autoImplicit false
namespace PV_RJ4IDB
structure ClientSuffix where
 writeProof : Trace Unit
 writeStatement : Unit → Trace Unit
 makeReturnedJSON : Unit → Trace Bytes
 printStdout : Bytes → Trace Unit

def planSuffix (o : ClientSuffix) : Trace Bytes :=
 bind o.writeProof (fun u => bind (o.writeStatement u) o.makeReturnedJSON)

def mainSuffix (o : ClientSuffix) : Trace Unit :=
 bind (planSuffix o) o.printStdout

theorem main_order (o : ClientSuffix) :
 mainSuffix o = bind o.writeProof (fun u =>
 bind (o.writeStatement u) (fun v => bind (o.makeReturnedJSON v) o.printStdout)) := by
 unfold mainSuffix planSuffix
 rw [bind_assoc]
 congr 1
 funext u
 exact bind_assoc (o.writeStatement u) o.makeReturnedJSON o.printStdout

theorem statement_failure_preserves_proof (o : ClientSuffix) (es fs : List Event)
 (error : Bytes) (hp : o.writeProof = ⟨es,.success ()⟩)
 (hs : o.writeStatement () = ⟨fs,.failure error⟩) :
 mainSuffix o = ⟨es++fs,.failure error⟩ := by
 rw [main_order,hp]
 simp [bind,hs,prepend]

theorem json_divergence_preserves_files (o : ClientSuffix) (a b c : List Event)
 (hp : o.writeProof = ⟨a,.success ()⟩)
 (hs : o.writeStatement () = ⟨b,.success ()⟩)
 (hj : o.makeReturnedJSON () = ⟨c,.diverge⟩) :
 mainSuffix o = ⟨a++(b++c),.diverge⟩ := by
 rw [main_order,hp]
 simp [bind,hs,hj,prepend]
#print axioms main_order
#print axioms statement_failure_preserves_proof
#print axioms json_divergence_preserves_files
end PV_RJ4IDB
