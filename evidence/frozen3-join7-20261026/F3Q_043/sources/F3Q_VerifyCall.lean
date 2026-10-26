import Port9OR_BatchStep

import Port4B_VerifyInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_VerifyCall
open Aeneas Aeneas.Std Result MultiproofConeRef

theorem returned {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) (s : reference.Scratch) (nodes : Slice U8)
    (outIdx : Port9OR_BatchStep.Indices) (outVal : Port9OR_BatchStep.Values)
    (success : Port4B_VerifyInstall.verify D hash Port3_NativeBatchBody.multiproof.Arity.Two
      root s.idx s.val s.n nodes=ok (true,outIdx,outVal)) :
    ∃ out,reference.verify_owned (Port4B_VerifyInstall.digest D) hash root {s with «at»:=0#usize} nodes=
      ok (true,out) ∧ out.idx=outIdx ∧ out.val=outVal := by
  change (do
    let (accepted,out) ← reference.verify_owned (Port4B_VerifyInstall.digest D) hash
      root {s with «at»:=0#usize} nodes
    ok (accepted,out.idx,out.val))=ok (true,outIdx,outVal) at success
  obtain ⟨⟨accepted,out⟩,call,returned⟩ := Port3_PushFrame.bind_success _ _ _ success
  have same := Result.ok.inj returned
  simp only [Prod.mk.injEq] at same
  rcases same with ⟨truth,indices,values⟩
  subst accepted
  exact ⟨out,call,indices,values⟩

#print axioms returned
end AspisR1.F3Q_VerifyCall
end
