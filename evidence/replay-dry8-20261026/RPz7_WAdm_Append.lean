import RPz7_WAdm_SourceBody
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.WAdm_Append
open OraclePortCkptAbi2Extracted aspis_r1_cost_probe.verifier
open CheckpointBytes3Namespaces CheckpointBytesDigest WAdm_SourceBody
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep MultiproofConeCanonical

theorem roots (p : Prepared) :
    p.roots.val.flatMap (fun r => bytesOf r.val) =
    bytes (stateOf (p.roots.val[0]'(by simp [p.roots.property]))) ++
    bytes (stateOf (p.roots.val[1]'(by simp [p.roots.property]))) := by
  calc
    _ = [p.roots.val[0]'(by simp [p.roots.property]),p.roots.val[1]'(by simp [p.roots.property])].flatMap
        (fun r => bytesOf r.val) := congrArg (List.flatMap _) (two p.roots)
    _ = _ := by simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,bytes_stateOf]

theorem alpha (p : Prepared) :
    p.alpha.val.flatMap put =
      put (p.alpha.val[0]'(by simp [p.alpha.property])) ++
      put (p.alpha.val[1]'(by simp [p.alpha.property])) := by
  calc
    _ = [p.alpha.val[0]'(by simp [p.alpha.property]),p.alpha.val[1]'(by simp [p.alpha.property])].flatMap put :=
      congrArg (List.flatMap _) (two p.alpha)
    _ = _ := by simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]

theorem scalars {n : Nat} (xs : List aspis_core.field.QM31) (size : xs.length = n) :
    xs.flatMap putK = CheckpointBytesBlocks.rawKs
      (fun j : Fin n => xs[j.val]'(by rw [size]; exact j.isLt)) := by
  exact congrArg (List.flatMap putK) (ofFn_array xs size).symm

theorem coordinates (p : Prepared) (a : Accumulator) (size : a.weights.val.length = 64)
    (qb : ∀ j : Fin 22, (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val < 262144) :
    p.z.val.flatMap (fun z => putK z.x ++ putK z.y) =
      CheckpointBytesBlocks.rawKs (CheckpointBytesBody.fields p a size qb).coordinates := by
  calc
    _ = [p.z.val[0]'(by simp [p.z.property]),p.z.val[1]'(by simp [p.z.property])].flatMap
        (fun z => putK z.x ++ putK z.y) := congrArg (List.flatMap _) (two p.z)
    _ = _ := by
      simp only [CheckpointBytesBlocks.rawKs,CheckpointBytesBody.fields,List.ofFn_succ,List.ofFn_zero,
        Fin.val_zero,Fin.val_succ,List.flatMap_cons,List.flatMap_nil,List.append_nil,putK]
      simp only [List.append_assoc]

#print axioms roots
#print axioms alpha
#print axioms scalars
#print axioms coordinates
end AspisR1.WAdm_Append
end
