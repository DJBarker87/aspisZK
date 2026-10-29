import Port4C_QueryValues
import NEB_GeometryFieldPorts
set_option autoImplicit false
noncomputable section
namespace NEB_QueryNodeDomains
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open Port3_NativeQueryBody

def install (ops : Ops) : Ops :=
  {ops with
    op7 := AspisR1Qm31ArithmeticProbe.field.M31.mul
    op8 := AspisR1Qm31ArithmeticProbe.field.M31.double
    op5 := ok 1#u32
    op6 := AspisR1Qm31ArithmeticProbe.field.M31.sub}

/-- The square's selected domain is all raw words. The exact same returned
square establishes double's canonical domain, and that reply plus ONE
establish subtract's domain. No canonicality of the raw geometry z or child
success is an independent caller premise. -/
theorem reached (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
    (a out : verifier.Accumulator)
    (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (b bout : verifier.BatchedWeights)
    (o : Port4C_QueryValues.Observation (install ops) proof p a out g obs geometry b bout) :
    AspisR1Qm31ArithmeticProbe.field.M31.mul o.z o.z=ok o.square ∧
    o.square.val<2147483647 ∧
    AspisR1Qm31ArithmeticProbe.field.M31.double o.square=ok o.doubled ∧
    o.doubled.val<2147483647 ∧ o.one=1#u32 ∧
    AspisR1Qm31ArithmeticProbe.field.M31.sub o.doubled o.one=ok o.node ∧
    o.node.val<2147483647 := by
  have square : AspisR1Qm31ArithmeticProbe.field.M31.mul o.z o.z=ok o.square := o.square_call
  obtain ⟨s,hs,_,cs⟩ := ExtractedCurrentReducer.current_mul_mod o.z o.z
  have sameS : s=o.square := Result.ok.inj (hs.symm.trans square)
  have cSquare : o.square.val<2147483647 := sameS ▸ cs
  have doubled : AspisR1Qm31ArithmeticProbe.field.M31.double o.square=ok o.doubled := o.double_call
  obtain ⟨d,hd,_,cd⟩ := ExtractedCurrentM31AddSub.current_add_mod o.square o.square cSquare cSquare
  have actualD : AspisR1Qm31ArithmeticProbe.field.M31.double o.square=ok d := by
    simpa only [AspisR1Qm31ArithmeticProbe.field.M31.double] using hd
  have sameD : d=o.doubled := Result.ok.inj (actualD.symm.trans doubled)
  have cDouble : o.doubled.val<2147483647 := sameD ▸ cd
  have one : o.one=1#u32 := Result.ok.inj o.one_call |>.symm
  have cOne : o.one.val<2147483647 := by rw [one];decide
  have sub : AspisR1Qm31ArithmeticProbe.field.M31.sub o.doubled o.one=ok o.node := o.node_call
  obtain ⟨n,hn,_,cn⟩ := ExtractedCurrentM31AddSub.current_sub_mod o.doubled o.one cDouble cOne
  have sameN : n=o.node := Result.ok.inj (hn.symm.trans sub)
  exact ⟨square,cSquare,doubled,cDouble,one,sub,sameN ▸ cn⟩

/-- The witness comes from the SAME parent query Result; no new child run is
selected. Observer native fidelity remains an explicitly open obligation. -/
theorem accepted (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
    (a out : verifier.Accumulator)
    (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (b bout : verifier.BatchedWeights)
    (run : verifier.candidate.query_values (install ops) proof p a g obs geometry b=ok (.Ok (out,bout))) :
    ∃ o : Port4C_QueryValues.Observation (install ops) proof p a out g obs geometry b bout,
      o.square.val<2147483647 ∧ o.doubled.val<2147483647 ∧ o.node.val<2147483647 := by
  obtain ⟨o⟩ := Port4C_QueryValues.observed _ proof p a out g obs geometry b bout run
  have h := reached ops proof p a out g obs geometry b bout o
  exact ⟨o,h.2.1,h.2.2.2.1,h.2.2.2.2.2.2⟩

#print axioms reached
#print axioms accepted
end NEB_QueryNodeDomains
end
