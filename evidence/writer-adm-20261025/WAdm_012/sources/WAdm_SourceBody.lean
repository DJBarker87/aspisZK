import WAdm_Inventory
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.WAdm_SourceBody
open OraclePortCkptAbi2Extracted aspis_r1_cost_probe.verifier
open CheckpointBytes3Namespaces CheckpointBytesDigest
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep MultiproofConeCanonical

/-- Raw source put/put_k semantics, retaining the exact physical limb order. -/
def put (x : aspis_core.field.wide_exact.WideExact) : Bytes :=
  bytesOf (CheckpointBytesE.rawBytes x)
def putK (x : aspis_core.field.QM31) : Bytes := CheckpointBytesBlocks.rawK x

def tag : aspis_r1_cost_probe.transport.CheckpointAbi2Variant → U8
  | .S1 => 1#u8 | .S2 => 2#u8 | .D => 3#u8

/-- Content interpretation of verifier.rs:326-340's append sequence. It has
no selector call or selector failure fallback. Native Vec allocation and
physical carrier interpretation remain at the external runtime boundary. -/
def body (p : Prepared) (a : Accumulator) (hp hu : Array U8 32#usize) : Bytes :=
  OraclePortPhysicalFrameDraft.magic ++
  bytesOf [tag p.variant,UScalar.cast .U8 a.next,1#u8,0#u8,0#u8,0#u8,0#u8,0#u8] ++
  bytesOf hp.val ++ bytesOf hu.val ++ bytesOf p.state.val ++
  (p.roots.val.flatMap (fun root => bytesOf root.val)) ++
  put p.gamma ++ put p.kappa ++ (p.alpha.val.flatMap put) ++ putK p.rho ++
  (p.queries.val.flatMap (fun q => bytesOf (core.num.U32.to_le_bytes q).val)) ++
  (p.semantic_alpha.val.flatMap putK) ++
  (p.z.val.flatMap (fun z => putK z.x ++ putK z.y)) ++
  put p.claim ++ put a.rhs ++ putK a.power ++ (a.weights.val.flatMap putK)

theorem ofFn_array {A : Type} {n : Nat} (xs : List A) (size : xs.length = n) :
    (List.ofFn (fun j : Fin n => xs[j.val]'(by rw [size]; exact j.isLt))) = xs := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,size]
  · intro i hi hj
    simp only [List.getElem_ofFn]

theorem two {A : Type} (xs : Array A 2#usize) :
    xs.val = [xs.val[0]'(by simp [xs.property]),xs.val[1]'(by simp [xs.property])] := by
  have h := ofFn_array xs.val (show xs.val.length = 2 from xs.property)
  simpa only [List.ofFn_succ,List.ofFn_zero,List.cons_append,List.nil_append,List.append_nil,Fin.val_zero,Fin.val_succ] using h.symm

theorem flatMap_ofFn {A B : Type} {n : Nat} (f : Fin n → A) (g : A → List B) :
    (List.ofFn f).flatMap g = (List.ofFn (fun i => g (f i))).flatten := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.ofFn_succ,List.flatMap_cons,List.flatten_cons]
    rw [ih]

theorem queries (p : Prepared) (a : Accumulator) (size : a.weights.val.length = 64)
    (qb : ∀ j : Fin 22, (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val < 262144) :
    p.queries.val.flatMap (fun q => bytesOf (core.num.U32.to_le_bytes q).val) =
      OraclePortCheckpointAbiC5.queryBytes (CheckpointBytesBody.fields p a size qb).queries := by
  simp only [OraclePortCheckpointAbiC5.queryBytes,CheckpointBytesBody.fields]
  calc
    _ = (List.ofFn (fun j : Fin 22 => p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt))).flatMap
        (fun q => bytesOf (core.num.U32.to_le_bytes q).val) :=
      congrArg (List.flatMap _) (ofFn_array p.queries.val (show p.queries.val.length = 22 from p.queries.property)).symm
    _ = _ := by
      simp only [flatMap_ofFn]
      congr 2
      funext i
      exact CheckpointP6KBytes.word_bytes _

#print axioms ofFn_array
#print axioms two
#print axioms flatMap_ofFn
#print axioms queries
end AspisR1.WAdm_SourceBody
end
