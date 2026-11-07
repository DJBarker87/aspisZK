import NMS_RSL241Fold
set_option autoImplicit false
namespace NMS_RSL241Weak
open RSL RSL.TX2_241 NMS_RSL241Replay
/-- Definitional specialization at precisely the TCK weak interface shape.
This is a source-relational theorem, with the same pending interpretation
as NMS_RSL241Fold.fold. It is not a native row root. -/
theorem fold (L : PoolLib) (D : DeployedIds) (V : V2Lib)
 (w : Bytes → Bytes → Bytes → Spec (Except V.VErr Unit))
 (validate : TX2_242.Args → Env → Obs (Except ProgramError (TX2_242.Validated L)))
 (child242 : TX2_242.RowSpec_242 L D validate)
 (scan : NMS_RSL242Facts.ScannerExtent L)
 (verify : VerifyNative {V with Root0 := fun _ _ => True,tx2auth := w})
 (child064 : VerifyPacket {V with Root0 := fun _ _ => True,tx2auth := w} verify)
 (a : Args) (consistent : ∀ x ∈ a.accounts, Consistent x) :
 NMS_RSLRefine.Refines
  (replay L {V with Root0 := fun _ _ => True,tx2auth := w} validate verify a)
  (Ref L D {V with Root0 := fun _ _ => True,tx2auth := w} a) :=
 NMS_RSL241Fold.fold L D _ validate child242 scan verify child064 a
  ⟨consistent,fun _ _ _ _ _ _ _ _ _ _ => trivial⟩
#print axioms fold
end NMS_RSL241Weak
