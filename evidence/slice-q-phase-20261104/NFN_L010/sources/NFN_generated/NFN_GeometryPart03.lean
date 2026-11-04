import Lean
import NFN_PhaseTransport
import NFN_ReserveOwner
import NFN_GeometryPart02
import NBG_Constructors
import NEB_PureFrame
import NDH_Geometry
import R17CurrentCM31Semantics
import Port3_PushFrame
import NEA_LineTail
import NEW_GeometryActual.Funs
import JFv_RawExtractedSemanticCallOpsV20
import NFB_RowRef.Funs
import Port5Q1_GeometryCanonical
import NEA_Index

-- BEGIN copied NEB_PointCalls: evidence/slice-q-compose-20261029/NEB_PointCalls.lean
set_option autoImplicit false
namespace NFN_NEB_PointCalls
open Aeneas Aeneas.Std Result AspisR1QueryGeometryActual

/-- The callee's non-root physical interpretation is instantiated, not retained. -/
theorem canonical_point (u : Usize) (admitted : NFN_NEA_PointBridge.PacketDomain u) :
    ∃ p : domain.Point field.M31,
      fast_domain.fibre_point NFN_NEA_FieldProduct.ops u=ok p ∧
      p.x.val<2147483647 ∧ p.y.val<2147483647 := by
  obtain ⟨a,b,z,canonical,_,_,point⟩ :=
    NFN_NEA_PointComplete.cohort NFN_NEA_FieldProduct.ops NFN_NEA_PointComplete.emitted_interpretation u admitted
  exact ⟨⟨z.a,z.b⟩,point,canonical.1,canonical.2⟩

/-- Exact selected operands establish the lower CM31 packet at this call. -/
theorem selected_product (u : Usize) (admitted : NFN_NEA_PointBridge.PacketDomain u) :
    ∃ (iA iB : Usize) (a b : U32 × U32) (z : field.CM31),
      lift (u &&& 511#usize)=ok iA ∧ u >>> 9#i32=ok iB ∧
      Array.index_usize fast_domain.TABLE_A iA=ok a ∧
      Array.index_usize fast_domain.TABLE_B iB=ok b ∧
      NFN_NEA_FieldProduct.Canonical ⟨a.1,a.2⟩ ∧
      NFN_NEA_FieldProduct.Canonical ⟨b.1,b.2⟩ ∧
      NFN_NEA_FieldProduct.ops.mul ⟨a.1,a.2⟩ ⟨b.1,b.2⟩=ok z ∧
      NFN_NEA_FieldProduct.Canonical z ∧
      fast_domain.fibre_point NFN_NEA_FieldProduct.ops u=ok ⟨z.a,z.b⟩ := by
  obtain ⟨ix,iA,iB,a,b,get,same,mask,lo,shift,hi,readA,readB⟩ :=
    R17FibrePointActualSuccess.source_indices_and_table_reads u admitted
  have eq : ix=u := (Result.ok.inj get).symm
  subst ix
  have low : iA.val<512 := by rw [lo]; exact Nat.mod_lt _ (by decide)
  have high : iB.val<512 := by rw [hi]; unfold NFN_NEA_PointBridge.PacketDomain at admitted; omega
  have ca := NEA_TableCanonical.readA iA low a readA
  have cb := NEA_TableCanonical.readB iB high b readB
  obtain ⟨z,product,cz,_⟩ := NFN_NEA_PointComplete.emitted_interpretation.multiply
    ⟨a.1,a.2⟩ ⟨b.1,b.2⟩ ca cb
  have selected := NFN_NEA_PointBridge.selected NFN_NEA_FieldProduct.ops u iA iB a b z
    mask shift readA readB NFN_NEA_PointComplete.emitted_interpretation.constructor product
  exact ⟨iA,iB,a,b,z,mask,shift,readA,readB,ca,cb,product,cz,selected.2⟩

def pureState {A S Event : Type} (s : S) (r : Result A) : Result (A × S × List Event) := do
  let z ← r
  ok (z,s,[])

/-- The emitted field/table operations are pure; the native bridge separately
certifies its ghost-only frame. This lift is not a native evaluator. -/
theorem state_effects {S Event : Type} (s : S) (u : Usize)
    (admitted : NFN_NEA_PointBridge.PacketDomain u) :
    ∃ p : domain.Point field.M31,
      pureState (Event:=Event) s (fast_domain.fibre_point NFN_NEA_FieldProduct.ops u)=ok (p,s,[]) ∧
      p.x.val<2147483647 ∧ p.y.val<2147483647 := by
  obtain ⟨p,run,cx,cy⟩ := canonical_point u admitted
  exact ⟨p,by simp only [pureState,run,bind_tc_ok],cx,cy⟩

#print axioms canonical_point
#print axioms selected_product
#print axioms state_effects
end NFN_NEB_PointCalls
-- END copied NEB_PointCalls
-- BEGIN copied NEB_TableCalls: evidence/slice-q-compose-20261029/NEB_TableCalls.lean
set_option autoImplicit false
namespace NFN_NEB_TableCalls
open Aeneas Aeneas.Std Result AspisR1QueryGeometryActual

def fromPublic (x : AspisR1PublicPreparation.aspis_core.field.CM31) : field.CM31 := ⟨x.a,x.b⟩

/-- Actual emitted constructor, both full raw words, and the exact table-call
carrier. No canonicality or successful-child premise is introduced. -/
theorem constructor (a b : U32) :
    AspisR1PublicPreparation.aspis_core.field.CM31.new a b=ok ⟨a,b⟩ ∧
    NFN_NEA_FieldProduct.ops.new a b=ok ⟨a,b⟩ ∧
    (do let x ← AspisR1PublicPreparation.aspis_core.field.CM31.new a b
        ok (fromPublic x))=NFN_NEA_FieldProduct.ops.new a b := by
  exact ⟨NBG_Constructors.cm31_new a b,rfl,by rw [NBG_Constructors.cm31_new];rfl⟩

theorem table_body (a b : U32) :
    fast_domain.table_value NFN_NEA_FieldProduct.ops (a,b)=NFN_NEA_FieldProduct.ops.new a b ∧
    fast_domain.table_value NFN_NEA_FieldProduct.ops (a,b)=ok ⟨a,b⟩ := ⟨rfl,rfl⟩

/-- The selected old table packet's dictionary and the point packet's emitted
field dictionary agree on this ACTUAL constructor call; multiplication unused. -/
theorem selected_table (v : U32 × U32) :
    (do let w ← NDH_Reference.table_ref v;ok (field.CM31.mk w.1 w.2))=
      fast_domain.table_value R17CurrentCM31Semantics.operations v ∧
    fast_domain.table_value R17CurrentCM31Semantics.operations v=
      fast_domain.table_value NFN_NEA_FieldProduct.ops v := by
  rcases v with ⟨a,b⟩
  exact ⟨NDH_Geometry.table _ (fun _ _ => rfl) _,rfl⟩

theorem constructor_frame {S Event : Type} (state : S) (a b : U32) :
    AspisR1PublicPreparation.aspis_core.field.CM31.new a b=ok ⟨a,b⟩ ∧
    NEB_PureFrame.run (Event:=Event) state
      (AspisR1PublicPreparation.aspis_core.field.CM31.new a b)=ok (⟨a,b⟩,state,[]) :=
  ⟨NBG_Constructors.cm31_new a b,NEB_PureFrame.successful state _ _ (NBG_Constructors.cm31_new a b)⟩

theorem table_frame {S Event : Type} (state : S) (v : U32 × U32) :
    fast_domain.table_value R17CurrentCM31Semantics.operations v=ok ⟨v.1,v.2⟩ ∧
    fast_domain.table_value NFN_NEA_FieldProduct.ops v=ok ⟨v.1,v.2⟩ ∧
    NDH_Reference.table_ref v=ok v ∧
    NEB_PureFrame.run (Event:=Event) state
      (fast_domain.table_value NFN_NEA_FieldProduct.ops v)=ok (⟨v.1,v.2⟩,state,[]) := by
  cases v with
  | mk a b => exact ⟨rfl,rfl,rfl,NEB_PureFrame.successful state _ _ rfl⟩

theorem getter_frame {S Event : Type} (state : S) (u : Usize) (admitted : u.val<262144) :
    domain.FibreIndex.get u=ok u ∧ NDH_Reference.fibre_get_ref u=ok u ∧
    NEB_PureFrame.run (Event:=Event) state (domain.FibreIndex.get u)=ok (u,state,[]) :=
  ⟨rfl,rfl,NEB_PureFrame.successful state _ _ rfl⟩

#print axioms constructor
#print axioms table_body
#print axioms selected_table
#print axioms constructor_frame
#print axioms table_frame
#print axioms getter_frame
end NFN_NEB_TableCalls
-- END copied NEB_TableCalls
-- BEGIN copied NEB_PointSuccess: evidence/slice-q-compose-20261029/NEB_PointSuccess.lean
set_option autoImplicit false
namespace NFN_NEB_PointSuccess
open Aeneas Aeneas.Std Result AspisR1QueryGeometryActual
open AspisR1.Port3_PushFrame (bind_success)

theorem read_bound {T : Type} {n : Usize} (a : Array T n) (i : Usize) (x : T)
    (read : Array.index_usize a i=ok x) : i.val<n.val := by
  by_contra bad
  have length : a.val.length=n.val := a.property
  have absent : a.val[i.val]?=none := List.getElem?_eq_none (by omega)
  simp [Array.index_usize,absent] at read

/-- Successful output canonicality does not require an independent valid-index
hypothesis: the SAME execution's successful reads establish both table domains. -/
theorem canonical (u : Usize) (point : domain.Point field.M31)
    (run : fast_domain.fibre_point NFN_NEA_FieldProduct.ops u=ok point) :
    point.x.val<2147483647 ∧ point.y.val<2147483647 := by
  unfold fast_domain.fibre_point at run
  obtain ⟨ix,_,run⟩ := bind_success _ _ _ run
  obtain ⟨iA,_,run⟩ := bind_success _ _ _ run
  obtain ⟨a,readA,run⟩ := bind_success _ _ _ run
  obtain ⟨left,leftRun,run⟩ := bind_success _ _ _ run
  obtain ⟨iB,_,run⟩ := bind_success _ _ _ run
  obtain ⟨b,readB,run⟩ := bind_success _ _ _ run
  obtain ⟨right,rightRun,run⟩ := bind_success _ _ _ run
  obtain ⟨product,mul,finalRun⟩ := bind_success _ _ _ run
  have ca := NEA_TableCanonical.readA iA (read_bound _ _ _ readA) a readA
  have cb := NEA_TableCanonical.readB iB (read_bound _ _ _ readB) b readB
  have la : fast_domain.table_value NFN_NEA_FieldProduct.ops a=ok ⟨a.1,a.2⟩ := by cases a; rfl
  have lb : fast_domain.table_value NFN_NEA_FieldProduct.ops b=ok ⟨b.1,b.2⟩ := by cases b; rfl
  have sameLeft := Result.ok.inj (leftRun.symm.trans la)
  have sameRight := Result.ok.inj (rightRun.symm.trans lb)
  rw [sameLeft,sameRight] at mul
  obtain ⟨z,productRun,cz,_⟩ := NFN_NEA_PointComplete.emitted_interpretation.multiply
    ⟨a.1,a.2⟩ ⟨b.1,b.2⟩ ca cb
  have same : product=z := Result.ok.inj (mul.symm.trans productRun)
  subst product
  have samePoint : point=({x:=z.a,y:=z.b} : domain.Point field.M31) :=
    (Result.ok.inj finalRun).symm
  rw [samePoint]
  exact cz

#print axioms read_bound
#print axioms canonical
end NFN_NEB_PointSuccess
-- END copied NEB_PointSuccess
-- BEGIN copied NEA_LineComplete: evidence/slice-q-leaves-20261029/NEA_LineComplete.lean
set_option autoImplicit false
namespace NFN_NEA_LineComplete
open Aeneas Aeneas.Std Result AspisR1QueryGeometryActual

theorem cohort (cm : CM31Ops) (physical : NFN_NEA_PointComplete.PhysicalInterpretation cm)
    (u : Usize) (admitted : NFN_NEA_PointBridge.PacketDomain u) :
    ∃ (p : domain.Point field.M31) (square out : U32),
      fast_domain.fibre_point cm u=ok p ∧
      p.x.val<2147483647 ∧ p.y.val<2147483647 ∧
      AspisR1Qm31ArithmeticProbe.field.M31.mul p.x p.x=ok square ∧
      square.val=(p.x.val*p.x.val)%2147483647 ∧
      NEA_Reference.line_double_sub_ref square=ok out ∧
      R17FibrePointLineNodeActual.line_node cm R17CurrentM31Semantics.operations u=ok out ∧
      out.val<2147483647 := by
  obtain ⟨a,b,z,canonical,_,_,point⟩ := NFN_NEA_PointComplete.cohort cm physical u admitted
  obtain ⟨square,product,value,cs⟩ := AspisR1.ExtractedCurrentReducer.current_mul_mod z.a z.a
  obtain ⟨d,add,_,cd⟩ := AspisR1.ExtractedCurrentM31AddSub.current_add_mod square square cs cs
  have doubled : AspisR1Qm31ArithmeticProbe.field.M31.double square=ok d := by
    simpa only [AspisR1Qm31ArithmeticProbe.field.M31.double] using add
  obtain ⟨out,sub,_,co⟩ := AspisR1.ExtractedCurrentM31AddSub.current_sub_mod d 1#u32 cd (by decide)
  have reference : NEA_Reference.line_double_sub_ref square=ok out := by
    rw [NEA_LineTail.reference square cs,doubled]
    simpa only [bind_tc_ok] using sub
  have line : R17FibrePointLineNodeActual.line_node cm R17CurrentM31Semantics.operations u=ok out := by
    simp only [R17FibrePointLineNodeActual.line_node,point,bind_tc_ok,
      R17CurrentM31Semantics.operations,product,doubled,sub]
  exact ⟨⟨z.a,z.b⟩,square,out,point,canonical.1,canonical.2,product,value,reference,line,co⟩

#print axioms cohort
#print axioms AspisR1.ExtractedCurrentReducer.current_mul_mod
end NFN_NEA_LineComplete
-- END copied NEA_LineComplete
-- BEGIN copied NEB_LineCalls: evidence/slice-q-compose-20261029/NEB_LineCalls.lean
set_option autoImplicit false
namespace NFN_NEB_LineCalls
open Aeneas Aeneas.Std Result AspisR1QueryGeometryActual
open AspisR1.Port3_PushFrame (bind_success)

/-- Every inner point/field domain is discharged by the SAME emitted path. -/
theorem admitted (u : Usize) (domain : NFN_NEA_PointBridge.PacketDomain u) :
    ∃ (point : AspisR1QueryGeometryActual.domain.Point field.M31) (square out : U32),
      fast_domain.fibre_point NFN_NEA_FieldProduct.ops u=ok point ∧
      point.x.val<2147483647 ∧ point.y.val<2147483647 ∧
      AspisR1Qm31ArithmeticProbe.field.M31.mul point.x point.x=ok square ∧
      square.val<2147483647 ∧
      NEA_Reference.line_double_sub_ref square=ok out ∧
      R17FibrePointLineNodeActual.line_node NFN_NEA_FieldProduct.ops R17CurrentM31Semantics.operations u=ok out ∧
      out.val<2147483647 := by
  obtain ⟨p,square,out,point,cx,cy,product,value,reference,line,co⟩ :=
    NFN_NEA_LineComplete.cohort NFN_NEA_FieldProduct.ops NFN_NEA_PointComplete.emitted_interpretation u domain
  obtain ⟨s,run,_,cs⟩ := AspisR1.ExtractedCurrentReducer.current_mul_mod p.x p.x
  have same : s=square := Result.ok.inj (run.symm.trans product)
  exact ⟨p,square,out,point,cx,cy,product,same ▸ cs,reference,line,co⟩

/-- Even an unrestricted alias index can produce only canonical line output
on success; no second point-success or field-domain premise is introduced. -/
theorem successful (u : Usize) (out : U32)
    (run : R17FibrePointLineNodeActual.line_node NFN_NEA_FieldProduct.ops
      R17CurrentM31Semantics.operations u=ok out) : out.val<2147483647 := by
  unfold R17FibrePointLineNodeActual.line_node at run
  obtain ⟨p,point,run⟩ := bind_success _ _ _ run
  have cp := NFN_NEB_PointSuccess.canonical u p point
  obtain ⟨square,mul,run⟩ := bind_success _ _ _ run
  obtain ⟨d,doubled,run⟩ := bind_success _ _ _ run
  obtain ⟨s,product,_,cs⟩ := AspisR1.ExtractedCurrentReducer.current_mul_mod p.x p.x
  have sameSquare : square=s := Result.ok.inj (mul.symm.trans product)
  subst square
  obtain ⟨double,add,_,cd⟩ := AspisR1.ExtractedCurrentM31AddSub.current_add_mod s s cs cs
  have doubleRun : AspisR1Qm31ArithmeticProbe.field.M31.double s=ok double := by
    simpa only [AspisR1Qm31ArithmeticProbe.field.M31.double] using add
  have sameDouble : d=double := Result.ok.inj (doubled.symm.trans doubleRun)
  subst d
  obtain ⟨z,sub,_,cz⟩ := AspisR1.ExtractedCurrentM31AddSub.current_sub_mod double 1#u32 cd (by decide)
  have sameOut : out=z := Result.ok.inj (run.symm.trans sub)
  exact sameOut.symm ▸ cz

#print axioms admitted
#print axioms successful
end NFN_NEB_LineCalls
-- END copied NEB_LineCalls
-- BEGIN copied NEB_GeometryFieldPorts: evidence/slice-q-compose-20261029/NEB_GeometryFieldPorts.lean
set_option autoImplicit false
namespace NFN_NEB_GeometryFieldPorts
open Aeneas Aeneas.Std Result AspisR1 AspisR1QueryGeometryActual NFN_LPi_FieldValues

theorem add (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647) :
    FIo_Native.aspis_core.field.M31.add x y=AspisR1Qm31ArithmeticProbe.field.M31.add x y := by
  obtain ⟨a,ha,va,_⟩ := NFN_LPi_NatBase.add x y hx hy
  obtain ⟨b,hb,vb,_⟩ := ExtractedCurrentM31AddSub.current_add_mod x y hx hy
  have same : a=b := UScalar.eq_of_val_eq (va.trans vb.symm)
  rw [ha,hb,same]

theorem sub (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647) :
    FIo_Native.aspis_core.field.M31.sub x y=AspisR1Qm31ArithmeticProbe.field.M31.sub x y := by
  obtain ⟨a,ha,va,_⟩ := NFN_LPi_NatBase.sub x y hx hy
  obtain ⟨b,hb,vb,_⟩ := ExtractedCurrentM31AddSub.current_sub_mod x y hx hy
  have same : a=b := UScalar.eq_of_val_eq (va.trans vb.symm)
  rw [ha,hb,same]

theorem double (x : U32) (hx : x.val<2147483647) :
    FIo_Native.aspis_core.field.M31.double x=AspisR1Qm31ArithmeticProbe.field.M31.double x := by
  exact add x x hx hx

/-- Instantiate the ACTUAL adopted geometry dictionary, not only a new emitted
field dictionary with similar field names. -/
theorem physical : NFN_NEA_PointComplete.PhysicalInterpretation R17CurrentCM31Semantics.operations := by
  refine ⟨fun _ _ => rfl,?_⟩
  intro x y hx hy
  obtain ⟨z,run,cz,real,imag⟩ := ExtractedCurrentCM31Mul.current_mul_words
    (R17CurrentCM31Semantics.toArithmetic x) (R17CurrentCM31Semantics.toArithmetic y) hx hy
  refine ⟨R17CurrentCM31Semantics.fromArithmetic z,?_,cz,?_⟩
  · simp only [R17CurrentCM31Semantics.operations,run,bind_tc_ok]
  · apply Prod.ext
    · simpa only [R17CurrentCM31Semantics.fromArithmetic,R17CurrentCM31Semantics.toArithmetic,
        NFN_LPi_FieldValues.mulC,NFN_LPi_CMProduct.realWord,ExtractedCurrentCM31Mul.realWord] using real
    · simpa only [R17CurrentCM31Semantics.fromArithmetic,R17CurrentCM31Semantics.toArithmetic,
        NFN_LPi_FieldValues.mulC,NFN_LPi_CMProduct.imagWord,ExtractedCurrentCM31Mul.imagWord] using imag

theorem cm_eq (x y : field.CM31) (hx : NFN_NEA_FieldProduct.Canonical x) (hy : NFN_NEA_FieldProduct.Canonical y) :
    R17CurrentCM31Semantics.operations.mul x y=NFN_NEA_FieldProduct.ops.mul x y := by
  obtain ⟨a,ha,_,va⟩ := physical.multiply x y hx hy
  obtain ⟨b,hb,_,vb⟩ := NFN_NEA_PointComplete.emitted_interpretation.multiply x y hx hy
  have values : (a.a.val,a.b.val)=(b.a.val,b.b.val) := va.trans vb.symm
  have ae : a.a=b.a := UScalar.eq_of_val_eq (congrArg Prod.fst values)
  have be : a.b=b.b := UScalar.eq_of_val_eq (congrArg Prod.snd values)
  have same : a=b := by cases a;cases b;simp_all
  rw [ha,hb,same]

#print axioms add
#print axioms sub
#print axioms double
#print axioms physical
#print axioms cm_eq
#print axioms NFN_NBG_InverseBridge.mul_eq_probe
end NFN_NEB_GeometryFieldPorts
-- END copied NEB_GeometryFieldPorts
-- BEGIN copied NEW_GeometryArithmetic: evidence/slice-q-compose4-20261104/NEW_GeometryArithmetic.lean
set_option autoImplicit false
namespace NFN_NEW_GeometryArithmetic
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20
abbrev C := NEW_GeometryActual.aspis_core.field.CM31
abbrev NC := FIo_Native.aspis_core.field.CM31

def toC (x : C) : NC := ⟨x.a,x.b⟩
def fromC (x : NC) : C := ⟨x.a,x.b⟩

theorem roundtrip (x : C) : fromC (toC x)=x := by cases x; rfl

theorem reducer (x : U64) : NEW_GeometryActual.aspis_core.field.reduce_u64 x =
    FIo_Native.aspis_core.field.reduce_u64 x := by
  simp only [NEW_GeometryActual.aspis_core.field.reduce_u64,
    FIo_Native.aspis_core.field.reduce_u64,
    NEW_GeometryActual.aspis_core.field.P,FIo_Native.aspis_core.field.P]

theorem multiply (x y : U32) : NEW_GeometryActual.aspis_core.field.M31.mul x y =
    FIo_Native.aspis_core.field.M31.mul x y := by
  simp only [NEW_GeometryActual.aspis_core.field.M31.mul,
    FIo_Native.aspis_core.field.M31.mul,reducer]

theorem reduce_wrapper (x : U64) : NEW_GeometryActual.aspis_core.field.M31.reduce_u64 x =
    FIo_Native.aspis_core.field.M31.reduce_u64 x := by
  simp only [NEW_GeometryActual.aspis_core.field.M31.reduce_u64,
    FIo_Native.aspis_core.field.M31.reduce_u64,reducer]

theorem add (x y : U32) : NEW_GeometryActual.aspis_core.field.M31.add x y =
    FIo_Native.aspis_core.field.M31.add x y := by
  simp only [NEW_GeometryActual.aspis_core.field.M31.add,
    FIo_Native.aspis_core.field.M31.add,
    NEW_GeometryActual.aspis_core.field.P,FIo_Native.aspis_core.field.P]

theorem sub (x y : U32) : NEW_GeometryActual.aspis_core.field.M31.sub x y =
    FIo_Native.aspis_core.field.M31.sub x y := by
  simp only [NEW_GeometryActual.aspis_core.field.M31.sub,
    FIo_Native.aspis_core.field.M31.sub,
    NEW_GeometryActual.aspis_core.field.P,FIo_Native.aspis_core.field.P]

theorem double (x : U32) : NEW_GeometryActual.aspis_core.field.M31.double x =
    FIo_Native.aspis_core.field.M31.double x := by
  simp only [NEW_GeometryActual.aspis_core.field.M31.double,
    FIo_Native.aspis_core.field.M31.double,add]

theorem multiply_probe (x y : U32) : NEW_GeometryActual.aspis_core.field.M31.mul x y =
    AspisR1Qm31ArithmeticProbe.field.M31.mul x y :=
  (multiply x y).trans (NFN_NBG_InverseBridge.mul_eq_probe x y)

theorem double_probe (x : U32) (hx : x.val<2147483647) :
    NEW_GeometryActual.aspis_core.field.M31.double x =
      AspisR1Qm31ArithmeticProbe.field.M31.double x :=
  (double x).trans (NFN_NEB_GeometryFieldPorts.double x hx)

theorem sub_probe (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647) :
    NEW_GeometryActual.aspis_core.field.M31.sub x y =
      AspisR1Qm31ArithmeticProbe.field.M31.sub x y :=
  (sub x y).trans (NFN_NEB_GeometryFieldPorts.sub x y hx hy)

theorem square_body (iter : core.ops.range.Range Usize) (x : U32) :
    NEW_GeometryActual.aspis_core.field.square_n_loop.body iter x =
      NEW_InverseActual.aspis_core.field.square_n_loop.body iter x := by
  simp only [NEW_GeometryActual.aspis_core.field.square_n_loop.body,
    NEW_InverseActual.aspis_core.field.square_n_loop.body,multiply,NFN_NEW_InverseAssociation.multiply]
  rfl

theorem square_loop (iter : core.ops.range.Range Usize) (x : U32) :
    NEW_GeometryActual.aspis_core.field.square_n_loop iter x =
      NEW_InverseActual.aspis_core.field.square_n_loop iter x := by
  unfold NEW_GeometryActual.aspis_core.field.square_n_loop
    NEW_InverseActual.aspis_core.field.square_n_loop
  simp only [square_body]

theorem square (x : U32) (n : Usize) :
    NEW_GeometryActual.aspis_core.field.square_n x n =
      NEW_InverseActual.aspis_core.field.square_n x n := by
  simp only [NEW_GeometryActual.aspis_core.field.square_n,
    NEW_InverseActual.aspis_core.field.square_n,square_loop]

theorem inverse (x : U32) : NEW_GeometryActual.aspis_core.field.M31.inv x =
    Port4C_InverseExecution.inverse_owned x := by
  rw [←NFN_NEW_InverseAssociation.cohort]
  simp only [NEW_GeometryActual.aspis_core.field.M31.inv,
    NEW_InverseActual.aspis_core.field.M31.inv,multiply,NFN_NEW_InverseAssociation.multiply,square]

theorem map_okC (a b : U32) : resultMap toC (ok ({a,b} : C)) = ok ({a,b} : NC) := rfl

/-- Nominal record transport only; the existing arithmetic/domain proofs are reused. -/
theorem cm_multiply (x y : C) :
    resultMap toC (NEW_GeometryActual.aspis_core.field.CM31.mul x y) =
      FIo_Native.aspis_core.field.CM31.mul (toC x) (toC y) := by
  simp only [NEW_GeometryActual.aspis_core.field.CM31.mul,
    FIo_Native.aspis_core.field.CM31.mul,resultMap_bind,multiply,reduce_wrapper,sub,
    toC,map_okC]

#print axioms roundtrip
#print axioms reducer
#print axioms multiply
#print axioms reduce_wrapper
#print axioms add
#print axioms sub
#print axioms double
#print axioms multiply_probe
#print axioms double_probe
#print axioms sub_probe
#print axioms square_body
#print axioms square_loop
#print axioms square
#print axioms inverse
#print axioms map_okC
#print axioms cm_multiply
end NFN_NEW_GeometryArithmetic
-- END copied NEW_GeometryArithmetic
-- BEGIN copied NEW_GeometryPolynomial: evidence/slice-q-compose4-20261104/NEW_GeometryPolynomial.lean
set_option autoImplicit false
namespace NFN_NEW_GeometryPolynomial
open Aeneas Aeneas.Std Result AspisR1

def native (x : U32) : Result U32 := do
 let p ← NEW_GeometryActual.aspis_core.field.M31.mul x x
 let d ← NEW_GeometryActual.aspis_core.field.M31.double p
 NEW_GeometryActual.aspis_core.field.M31.sub d NEW_GeometryActual.aspis_core.field.M31.ONE

def cohort (x : U32) : Result U32 := do
 let p ← AspisR1Qm31ArithmeticProbe.field.M31.mul x x
 let d ← AspisR1Qm31ArithmeticProbe.field.M31.double p
 AspisR1Qm31ArithmeticProbe.field.M31.sub d 1#u32

/-- Product canonicality discharges BOTH later scalar domains, on every raw input. -/
theorem complete (x : U32) : native x = cohort x := by
 obtain ⟨p,product,_,cp⟩ := ExtractedCurrentReducer.current_mul_mod x x
 obtain ⟨d,doubled,_,cd⟩ := ExtractedCurrentM31AddSub.current_add_mod p p cp cp
 have doubleRun : AspisR1Qm31ArithmeticProbe.field.M31.double p=ok d := by
  simpa only [AspisR1Qm31ArithmeticProbe.field.M31.double] using doubled
 simp only [native,cohort,NFN_NEW_GeometryArithmetic.multiply_probe,product,bind_tc_ok,
  NFN_NEW_GeometryArithmetic.double_probe p cp,doubleRun,
  NEW_GeometryActual.aspis_core.field.M31.ONE,
  NFN_NEW_GeometryArithmetic.sub_probe d 1#u32 cd (by decide)]

theorem continuation {T : Type} (x : U32) (k : U32 → Result T) :
 (do let p ← NEW_GeometryActual.aspis_core.field.M31.mul x x
     let d ← NEW_GeometryActual.aspis_core.field.M31.double p
     let z ← NEW_GeometryActual.aspis_core.field.M31.sub d NEW_GeometryActual.aspis_core.field.M31.ONE
     k z) =
 (do let p ← AspisR1Qm31ArithmeticProbe.field.M31.mul x x
     let d ← AspisR1Qm31ArithmeticProbe.field.M31.double p
     let z ← AspisR1Qm31ArithmeticProbe.field.M31.sub d 1#u32
     k z) := by
 have same := congrArg (fun r : Result U32 => do let z ← r; k z) (complete x)
 simpa only [native,cohort,bind_assoc_eq,bind_tc_ok] using same

#print axioms complete
#print axioms continuation
end NFN_NEW_GeometryPolynomial
-- END copied NEW_GeometryPolynomial
-- BEGIN copied NFB_MulDischarge: evidence/slice-q-compose5-20261104/NFB_MulDischarge.lean
set_option autoImplicit false
namespace NFN_NFB_MulDischarge
open Aeneas Aeneas.Std Result AspisR1

/-- Every raw scalar operand is admitted. The complete emitted operation
returns ok with precisely the natural-number product specification and a
canonical reply. This discharges the local ordered-log product abstraction. -/
theorem multiplication (left right : U32) :
    ∃ reply : U32,
      NEW_GeometryActual.aspis_core.field.M31.mul left right=ok reply ∧
      reply.val=(left.val*right.val)%2147483647 ∧ reply.val<2147483647 := by
 obtain ⟨reply,run,value,canonical⟩ := ExtractedCurrentReducer.current_mul_mod left right
 exact ⟨reply,(NFN_NEW_GeometryArithmetic.multiply_probe left right).trans run,value,canonical⟩

/-- The caller's only numeric restriction on its arbitrary native product
reply is supplied by the operation above, for all possible raw line words. -/
theorem caller_product_domain (line : U32) :
    ∃ reply : U32,
      NEW_GeometryActual.aspis_core.field.M31.mul line line=ok reply ∧
      reply.val<2147483647 := by
 obtain ⟨reply,run,_,canonical⟩ := multiplication line line
 exact ⟨reply,run,canonical⟩

/-- Reuse NEW's contextual substitution; the downstream double/subtract
preconditions are derived from the SAME saved product, never caller premises. -/
theorem row_continuation {T : Type} (line : U32) (k : U32 → Result T) :
 (do let p ← NEW_GeometryActual.aspis_core.field.M31.mul line line
     let d ← NEW_GeometryActual.aspis_core.field.M31.double p
     let z ← NEW_GeometryActual.aspis_core.field.M31.sub d NEW_GeometryActual.aspis_core.field.M31.ONE
     k z) =
 (do let p ← AspisR1Qm31ArithmeticProbe.field.M31.mul line line
     let d ← AspisR1Qm31ArithmeticProbe.field.M31.double p
     let z ← AspisR1Qm31ArithmeticProbe.field.M31.sub d 1#u32
     k z) := NFN_NEW_GeometryPolynomial.continuation line k

#print axioms multiplication
#print axioms caller_product_domain
#print axioms row_continuation
end NFN_NFB_MulDischarge
-- END copied NFB_MulDischarge
-- BEGIN copied NFB_RowPrimitives: evidence/slice-q-compose5-20261104/NFB_RowPrimitives.lean
set_option autoImplicit false
namespace NFN_NFB_RowPrimitives
open Aeneas Aeneas.Std Result
namespace N
abbrev F := NFB_RowRef.aspis_core.field.M31
end N

theorem double (x : U32) : NFB_RowRef.aspis_core.field.M31.double x=
    NEW_GeometryActual.aspis_core.field.M31.double x := by
 simp only [NFB_RowRef.aspis_core.field.M31.double,
   NEW_GeometryActual.aspis_core.field.M31.double,
   NFB_RowRef.aspis_core.field.M31.add,
   NEW_GeometryActual.aspis_core.field.M31.add,
   NFB_RowRef.aspis_core.field.P,NEW_GeometryActual.aspis_core.field.P]

theorem subtract (x y : U32) : NFB_RowRef.aspis_core.field.M31.sub x y=
    NEW_GeometryActual.aspis_core.field.M31.sub x y := by
 simp only [NFB_RowRef.aspis_core.field.M31.sub,
   NEW_GeometryActual.aspis_core.field.M31.sub,
   NFB_RowRef.aspis_core.field.P,NEW_GeometryActual.aspis_core.field.P]

theorem index (u : Usize) : NFB_RowRef.aspis_core.r0.domain.FibreIndex.new u=
    if u<262144#usize then ok (.Ok u)
    else ok (.Err NFB_RowRef.aspis_core.r0.Error.IndexOutOfRange) := by rfl

theorem clone (word : U32) :
    NEW_GeometryActual.aspis_core.field.M31.Insts.CoreCloneClone.clone word=ok word := by rfl

#print axioms double
#print axioms subtract
#print axioms index
#print axioms clone
end NFN_NFB_RowPrimitives
-- END copied NFB_RowPrimitives
-- BEGIN copied NFB_RowLog: evidence/slice-q-compose5-20261104/NFB_RowLog.lean
set_option autoImplicit false
namespace NFN_NFB_RowLog
open Aeneas Aeneas.Std Result
abbrev Call := NFB_RowRef.NFB_RowCall
abbrev Log := NFB_RowRef.NFB_RowLog

def calls (c0 c1 c2 c3 : Call) : Array Call 4#usize := Array.make 4#usize [c0,c1,c2,c3]
def state (i : Usize) (c0 c1 c2 c3 : Call) : Log := ⟨calls c0 c1 c2 c3,i⟩
def event (kind : U8) (a b reply reply2 : U32) : Call := ⟨kind,a,b,reply,reply2⟩
def empty : Call := ⟨0#u8,0#u32,0#u32,0#u32,0#u32⟩
def initial : Log := state 0#usize empty empty empty empty

theorem step0 (c0 c1 c2 c3 : Call) (kind : U8) (a b r r2 : U32) :
 NFB_RowRef.NFB_row_call (state 0#usize c0 c1 c2 c3) kind a b r r2=
 ok (state 1#usize (event kind a b r r2) c1 c2 c3) := by
 have inc : Usize.wrapping_add 0#usize 1#usize=1#usize := by
  apply UScalar.eq_of_val_eq
  rw [Usize.wrapping_add_val_eq]
  have cap : 4 < UScalar.size .Usize := by rw [UScalar.size_def]; scalar_tac
  change (0+1)%UScalar.size .Usize=1
  rw [Nat.mod_eq_of_lt (by omega)]
 simp [NFB_RowRef.NFB_row_call,state,calls,event,Array.update,Array.getElem?_Usize_eq,Array.make,inc,lift,bind_tc_ok]

theorem step1 (c0 c1 c2 c3 : Call) (kind : U8) (a b r r2 : U32) :
 NFB_RowRef.NFB_row_call (state 1#usize c0 c1 c2 c3) kind a b r r2=
 ok (state 2#usize c0 (event kind a b r r2) c2 c3) := by
 have inc : Usize.wrapping_add 1#usize 1#usize=2#usize := by
  apply UScalar.eq_of_val_eq
  rw [Usize.wrapping_add_val_eq]
  have cap : 4 < UScalar.size .Usize := by rw [UScalar.size_def]; scalar_tac
  change (1+1)%UScalar.size .Usize=2
  rw [Nat.mod_eq_of_lt (by omega)]
 simp [NFB_RowRef.NFB_row_call,state,calls,event,Array.update,Array.getElem?_Usize_eq,Array.make,inc,lift,bind_tc_ok]

theorem step2 (c0 c1 c2 c3 : Call) (kind : U8) (a b r r2 : U32) :
 NFB_RowRef.NFB_row_call (state 2#usize c0 c1 c2 c3) kind a b r r2=
 ok (state 3#usize c0 c1 (event kind a b r r2) c3) := by
 have inc : Usize.wrapping_add 2#usize 1#usize=3#usize := by
  apply UScalar.eq_of_val_eq
  rw [Usize.wrapping_add_val_eq]
  have cap : 4 < UScalar.size .Usize := by rw [UScalar.size_def]; scalar_tac
  change (2+1)%UScalar.size .Usize=3
  rw [Nat.mod_eq_of_lt (by omega)]
 simp [NFB_RowRef.NFB_row_call,state,calls,event,Array.update,Array.getElem?_Usize_eq,Array.make,inc,lift,bind_tc_ok]

theorem step3 (c0 c1 c2 c3 : Call) (kind : U8) (a b r r2 : U32) :
 NFB_RowRef.NFB_row_call (state 3#usize c0 c1 c2 c3) kind a b r r2=
 ok (state 4#usize c0 c1 c2 (event kind a b r r2)) := by
 have inc : Usize.wrapping_add 3#usize 1#usize=4#usize := by
  apply UScalar.eq_of_val_eq
  rw [Usize.wrapping_add_val_eq]
  have cap : 4 < UScalar.size .Usize := by rw [UScalar.size_def]; scalar_tac
  change (3+1)%UScalar.size .Usize=4
  rw [Nat.mod_eq_of_lt (by omega)]
 simp [NFB_RowRef.NFB_row_call,state,calls,event,Array.update,Array.getElem?_Usize_eq,Array.make,inc,lift,bind_tc_ok]

#print axioms step0
#print axioms step1
#print axioms step2
#print axioms step3
end NFN_NFB_RowLog
-- END copied NFB_RowLog
-- BEGIN copied NEB_GeometryPrimitives: evidence/slice-q-compose-20261029/NEB_GeometryPrimitives.lean
set_option autoImplicit false
noncomputable section
namespace NFN_NEB_GeometryPrimitives
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open Port3_NativeGeometryBody
open Port3_PushFrame (bind_success)

/-- Install actual emitted field/point operations. Unrelated standard-library
and error ports remain those of the root physical interpretation. -/
def install {CoreError : Type} (ops : Ops CoreError) : Ops CoreError :=
  {ops with
    op15 := fun f => do
      let p ← AspisR1QueryGeometryActual.fast_domain.fibre_point NFN_NEA_FieldProduct.ops f
      ok ⟨p.x,p.y⟩
    op14 := R17FibrePointLineNodeActual.line_node NFN_NEA_FieldProduct.ops R17CurrentM31Semantics.operations
    op9 := AspisR1Qm31ArithmeticProbe.field.M31.mul
    op10 := AspisR1Qm31ArithmeticProbe.field.M31.double
    op8 := AspisR1Qm31ArithmeticProbe.field.M31.sub
    op7 := ok 1#u32}

/-- This discharges the inner SessionAPrimitives predicate; it is a theorem,
not a new caller premise or an assumed geometry-success conclusion. -/
theorem primitives {CoreError : Type} (ops : Ops CoreError) :
    Port5Q1_GeometryCanonical.SessionAPrimitives (install ops) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro f p run
    change (do let q ← AspisR1QueryGeometryActual.fast_domain.fibre_point NFN_NEA_FieldProduct.ops f
               ok ({x:=q.x,y:=q.y} : aspis_core.r0.domain.Point U32))=ok p at run
    obtain ⟨q,point,finalRun⟩ := bind_success _ _ _ run
    have cq := NFN_NEB_PointSuccess.canonical f q point
    have same : ({x:=q.x,y:=q.y} : aspis_core.r0.domain.Point U32)=p := Result.ok.inj finalRun
    rw [← same]
    exact cq
  · intro f x run
    exact NFN_NEB_LineCalls.successful f x run
  · intro x y z cx cy run
    obtain ⟨w,product,_,cw⟩ := AspisR1.ExtractedCurrentReducer.current_mul_mod x y
    have same : w=z := Result.ok.inj (product.symm.trans run)
    exact same ▸ cw
  · intro x y cx run
    obtain ⟨w,add,_,cw⟩ := AspisR1.ExtractedCurrentM31AddSub.current_add_mod x x cx cx
    have doubled : AspisR1Qm31ArithmeticProbe.field.M31.double x=ok w := by simpa only [AspisR1Qm31ArithmeticProbe.field.M31.double] using add
    have same : w=y := Result.ok.inj (doubled.symm.trans run)
    exact same ▸ cw
  · intro x run
    change ok 1#u32=ok x at run
    cases run
    change (1#u32).val<2147483647
    decide
  · intro x y z cx cy run
    obtain ⟨w,sub,_,cw⟩ := AspisR1.ExtractedCurrentM31AddSub.current_sub_mod x y cx cy
    have same : w=z := Result.ok.inj (sub.symm.trans run)
    exact same ▸ cw

#print axioms primitives
end NFN_NEB_GeometryPrimitives
end
-- END copied NEB_GeometryPrimitives
-- BEGIN copied NEB_GeometryIndices: evidence/slice-q-compose-20261029/NEB_GeometryIndices.lean
set_option autoImplicit false
noncomputable section
namespace NFN_NEB_GeometryIndices
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open Port3_NativeGeometryBody
open Port3_PushFrame (bind_success)

def indexPort {CoreError : Type} (error : CoreError) (u : Usize) :
    Result (core.result.Result Usize CoreError) := do
  let r ← NEA_Reference.fibre_new_ref u
  ok (match r with | .Ok f => .Ok f | .Err _ => .Err error)

def install {CoreError : Type} (ops : Ops CoreError) (error : CoreError) : Ops CoreError :=
  {NFN_NEB_GeometryPrimitives.install ops with op12:=indexPort error}

theorem accepted {CoreError : Type} (error : CoreError) (u f : Usize)
    (run : indexPort error u=ok (.Ok f)) : f=u ∧ f.val<262144 := by
  unfold indexPort at run
  obtain ⟨r,reference,run⟩ := bind_success _ _ _ run
  cases r with
  | Err e => cases run
  | Ok x =>
    cases Result.ok.inj run
    obtain ⟨same,bound⟩ := NEA_Index.accepted u f reference
    exact ⟨same,by rw [same];exact bound⟩

theorem admitted {CoreError : Type} (error : CoreError) (u : Usize)
    (bound : u.val<262144) : indexPort error u=ok (.Ok u) := by
  simp only [indexPort,NEA_Index.canonical_index u bound,bind_tc_ok]

theorem primitives {CoreError : Type} (ops : Ops CoreError) (error : CoreError) :
    Port5Q1_GeometryCanonical.SessionAPrimitives (install ops error) := by
  have p := NFN_NEB_GeometryPrimitives.primitives ops
  exact ⟨p.point,p.line,p.multiply,p.double,p.one,p.subtract⟩

/-- These are precisely the parent, left and right scalar expressions in the
emitted gather body. All index domains follow from its first accepted index. -/
theorem aligned {CoreError : Type} (error : CoreError) (u : Usize) (bound : u.val<262144) :
    ∃ parent left right : Usize,
      u / 4#usize=ok parent ∧
      left=Usize.wrapping_mul parent 4#usize ∧
      right=Usize.wrapping_add left 3#usize ∧
      left.val=u.val/4*4 ∧ right.val=u.val/4*4+3 ∧
      left.val<262144 ∧ right.val<262144 ∧
      indexPort error left=ok (.Ok left) ∧ indexPort error right=ok (.Ok right) := by
  obtain ⟨parent,division,value⟩ := UScalar.div_spec u (y:=4#usize) (by decide)
  have pv : parent.val=u.val/4 := value
  let left := Usize.wrapping_mul parent 4#usize
  let right := Usize.wrapping_add left 3#usize
  have cap : 262144 < UScalar.size .Usize := by rw [UScalar.size_def];scalar_tac
  have lv : left.val=u.val/4*4 := by
    dsimp only [left]
    rw [Usize.wrapping_mul_val_eq]
    change (parent.val*4)%UScalar.size .Usize=u.val/4*4
    rw [pv,Nat.mod_eq_of_lt (by omega)]
  have rv : right.val=u.val/4*4+3 := by
    dsimp only [right]
    rw [Usize.wrapping_add_val_eq]
    change (left.val+3)%UScalar.size .Usize=u.val/4*4+3
    rw [lv,Nat.mod_eq_of_lt (by omega)]
  have lb : left.val<262144 := by rw [lv];omega
  have rb : right.val<262144 := by rw [rv];omega
  exact ⟨parent,left,right,division,rfl,rfl,lv,rv,lb,rb,admitted error left lb,admitted error right rb⟩

#print axioms accepted
#print axioms admitted
#print axioms primitives
#print axioms aligned
end NFN_NEB_GeometryIndices
end
-- END copied NEB_GeometryIndices
-- BEGIN copied NFB_RowIndex: evidence/slice-q-compose5-20261104/NFB_RowIndex.lean
set_option autoImplicit false
namespace NFN_NFB_RowIndex
open Aeneas Aeneas.Std Result

theorem indexPort (u : Usize) : NFB_RowRef.aspis_core.r0.domain.FibreIndex.new u=
    NFN_NEB_GeometryIndices.indexPort NFB_RowRef.aspis_core.r0.Error.IndexOutOfRange u := by
 simp only [NFB_RowRef.aspis_core.r0.domain.FibreIndex.new,
   NFB_RowRef.aspis_core.r0.FIBRE_COUNT,bind_tc_ok,
   NFN_NEB_GeometryIndices.indexPort,NEA_Reference.fibre_new_ref]
 split <;> rfl

theorem admitted (u : Usize) (bound : u.val<262144) :
    NFB_RowRef.aspis_core.r0.domain.FibreIndex.new u=ok (.Ok u) := by
 rw [indexPort]
 exact NFN_NEB_GeometryIndices.admitted _ u bound

#print axioms indexPort
#print axioms admitted
end NFN_NFB_RowIndex
-- END copied NFB_RowIndex
-- BEGIN copied NFB_RowG: evidence/slice-q-compose5-20261104/NFB_RowG.lean
set_option autoImplicit false
namespace NFN_NFB_RowG
open Aeneas Aeneas.Std Result NFN_NFB_RowLog

def reply (x y left right product : U32) : Array U32 5#usize :=
 Array.make 5#usize [x,y,left,right,product]

def model (query x y lineX lineY product : U32) :
    Result (core.result.Result (Array U32 5#usize) NFB_RowRef.Error × NFB_RowRef.NFB_RowLog) := do
 let u ← lift (UScalar.cast .Usize query)
 if u<262144#usize then
  let parent ← u/4#usize
  let left ← lift (Usize.wrapping_mul parent 4#usize)
  let right ← lift (Usize.wrapping_add left 3#usize)
  let doubled ← NEW_GeometryActual.aspis_core.field.M31.double product
  let z ← NEW_GeometryActual.aspis_core.field.M31.sub doubled 1#u32
  ok (.Ok (Array.make 5#usize [x,y,lineX,lineY,z]),
   state 4#usize
    (event 1#u8 (UScalar.cast .U32 u) 0#u32 x y)
    (event 2#u8 (UScalar.cast .U32 left) 0#u32 lineX 0#u32)
    (event 3#u8 (UScalar.cast .U32 right) 0#u32 lineY 0#u32)
    (event 4#u8 lineX lineX product 0#u32))
 else ok (.Err .Query,initial)

/-- Exact local G: all replies are arbitrary and every Result and ordered
log entry is preserved. The only branch input is the real constructor domain;
left/right domains follow from it and are not hypotheses. -/
theorem complete (query x y lineX lineY product : U32) :
 NFB_RowRef.NFB_row query (reply x y lineX lineY product) initial=
 model query x y lineX lineY product := by
 let u := UScalar.cast .Usize query
 by_cases bound : u.val<262144
 · obtain ⟨parent,left,right,division,leftEq,rightEq,lv,rv,lb,rb,_,_⟩ :=
     NFN_NEB_GeometryIndices.aligned NFB_RowRef.aspis_core.r0.Error.IndexOutOfRange u bound
   have leftRun := NFN_NFB_RowIndex.admitted left lb
   have rightRun := NFN_NFB_RowIndex.admitted right rb
   have first := NFN_NFB_RowIndex.admitted u bound
   have guard : u<262144#usize := by exact bound
   dsimp only [u] at first guard division
   simp only [NFB_RowRef.NFB_row,model,reply,initial,
    first,division,←leftEq,←rightEq,leftRun,rightRun,
    NFB_RowRef.aspis_core.r0.domain.FibreIndex.get,
    core.result.Result.map_err,AspisR1.Port4C_GeometryStd.mapError,
    NFB_RowRef.NFB_row.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError,
    NFB_RowRef.NFB_row.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
    NFB_RowRef.NFB_row.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError,
    NFB_RowRef.NFB_row.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
    NFB_RowRef.NFB_row.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError,
    NFB_RowRef.NFB_row.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
    core.result.Result.Insts.CoreOpsTry.branch,
    Array.index_usize,Array.getElem?_Usize_eq,Array.make,
    NFB_RowRef.NFB_row_product,
    NFN_NFB_RowLog.step0,NFN_NFB_RowLog.step1,NFN_NFB_RowLog.step2,NFN_NFB_RowLog.step3,
    NFN_NFB_RowPrimitives.double,NFN_NFB_RowPrimitives.subtract,
    NFB_RowRef.aspis_core.field.M31.ONE,guard,if_true,lift,bind_tc_ok,uncurry]
   -- Only five literal reply positions remain; no recurrence is unfolded.
   simp
 · have guard : ¬u<262144#usize := by exact bound
   have first : NFB_RowRef.aspis_core.r0.domain.FibreIndex.new u=
       ok (.Err NFB_RowRef.aspis_core.r0.Error.IndexOutOfRange) := by
    rw [NFN_NFB_RowPrimitives.index,if_neg guard]
   dsimp only [u] at first guard
   simp only [NFB_RowRef.NFB_row,model,first,
    core.result.Result.map_err,AspisR1.Port4C_GeometryStd.mapError,
    NFB_RowRef.NFB_row.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError,
    NFB_RowRef.NFB_row.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    guard,if_false,lift,bind_tc_ok,uncurry]

#print axioms complete
end NFN_NFB_RowG
-- END copied NFB_RowG

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
