"""Success projections from emitted monadic binds, without expanding byte bodies."""
from pathlib import Path
D=Path('evidence/pv-b3p6-20261028/lean')
header='''import PV_B3P_BytesV3Emission226
import PV_B3P_ChunkV3Law226
import PV_B3P_ResultSuccess226
namespace {ns}
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_RustResult
set_option autoImplicit false
attribute [local irreducible] reference226.byte_at reference226.chunk8 reference226.chunk
'''
ns='PV_B3P_Chunk8Projection226';s=header.format(ns=ns)
s+='''set_option backward.isDefEq.respectTransparency false in
theorem success_cell (p : reference226.OwnedPublic) (base : Usize)
    (out : Array U8 8#usize) (h : reference226.chunk8 p base = .ok (.Ok out))
    (j : Usize) (hj : j.val < 8) :
    reference226.byte_at p (Usize.wrapping_add base j) =
      .ok (.Ok (out.val[j.val]'(by rw [out.property]; simpa using hj))) := by
  rw [PV_B3P_ChunkV3Law226.complete_result] at h
  unfold PV_B3P_ChunkV3Law226.spec8 at h
'''
for k in range(8):s+=f'  rw [PV_B3P_ResultSuccess226.bind_success] at h\n  obtain ⟨v{k},hv{k},h⟩ := h\n'
s+='  have he : Array.make 8#usize ['+','.join(f'v{k}' for k in range(8))+'] (by rfl) = out := core.result.Result.Ok.inj (Result.ok.inj h)\n  cases he\n'
s+='  have hc : '+' ∨ '.join(f'j.val = {k}' for k in range(8))+' := by omega\n  rcases hc with '+' | '.join(f'h{k}' for k in range(8))+'\n'
for k in range(8):s+=f'''  · have hje : j = {k}#usize := by apply UScalar.eq_of_val_eq; exact h{k}
    subst j
    have hval : ({k}#usize).val = {k} := rfl
    simpa only [hval,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] using hv{k}
'''
s+='#print axioms success_cell\nend '+ns+'\n';(D/f'{ns}.lean').write_text(s)
ns='PV_B3P_EncodeProjection226';s=header.format(ns=ns)
s+='''def start (q : Nat) (hq : q < 23) : Usize := Usize.ofNatCore (64*q) (by
  have hb := Usize.cMax_bound_concrete.1
  scalar_tac)
theorem start_val (q : Nat) (hq : q < 23) : (start q hq).val = 64*q := rfl
#print axioms start_val
set_option backward.isDefEq.respectTransparency false in
theorem success_chunk (p : reference226.OwnedPublic)
    (chunks : Array (Array U8 64#usize) 23#usize) (n : Usize)
    (h : reference226.encode_owned p = .ok (.Ok (chunks,n)))
    (q : Nat) (hq : q < 23) :
    reference226.chunk p (start q hq) =
      .ok (.Ok (chunks.val[q]'(by rw [chunks.property]; simpa using hq))) := by
  unfold reference226.encode_owned at h
  cases hw : p.withdrawal
  all_goals
    have hu : {p with withdrawal := p.withdrawal} = p := by cases p; rfl
    try simp only [hw] at hu
    simp only [hw,Bool.false_eq_true,↓reduceIte,lift,bind_tc_ok,hu,try_bind_eq] at h
'''
# Preserve the original p in the record-update calls before success decomposition.
for k in range(23):s+=f'    rw [PV_B3P_ResultSuccess226.bind_success] at h\n    obtain ⟨v{k},hv{k},h⟩ := h\n'
s+='    have he : (Array.make 23#usize ['+','.join(f'v{k}' for k in range(23))+'] (by rfl), (if p.withdrawal then 1427#usize else 1455#usize)) = (chunks,n) := by\n      simpa only [hw,Bool.false_eq_true,↓reduceIte] using core.result.Result.Ok.inj (Result.ok.inj h)\n    cases he\n'
s+='    have hc : '+' ∨ '.join(f'q = {k}' for k in range(23))+' := by omega\n    rcases hc with '+' | '.join('rfl' for k in range(23))+'\n'
for k in range(23):s+=f'''    · have hs : start {k} (by decide) = {64*k}#usize := by
        apply UScalar.eq_of_val_eq
        rfl
      simpa only [hs,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] using hv{k}
'''
s+='#print axioms success_chunk\nend '+ns+'\n';(D/f'{ns}.lean').write_text(s)
