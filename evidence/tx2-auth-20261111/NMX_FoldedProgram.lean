import NMX_Fold00
import NMX_S000Count
set_option autoImplicit false
noncomputable section
namespace NMX_FoldedProgram
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps
/-- Finite source-term factorization, with every typed continuation retained.
This does not unfold any child body or concrete input buffer. -/
theorem source (ops : Ops) (owners : Owners) (verifier : solana_pubkey.Pubkey)
 (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey)
 (outputLane : U8) (slot : U64) :
 NMX_SourceProgram.auth ops verifier accounts pool outputLane slot =
 (if Slice.len accounts != 7#usize then
  if Slice.len accounts < 7#usize then Program.reject .NotEnoughAccountKeys
  else Program.reject .InvalidArgument
 else NMX_Fold00.p001 owners ops verifier accounts pool outputLane slot) := by
 unfold NMX_SourceProgram.auth NMX_Fold00.p001 NMX_Fold00.p002 NMX_Fold00.p003 NMX_Fold00.p004 NMX_Fold00.p005 NMX_Fold00.p006 NMX_Fold00.p007 NMX_Fold00.p008 NMX_Fold00.p009 NMX_Fold00.p010 NMX_Fold01.p011 NMX_Fold01.p012 NMX_Fold01.p013 NMX_Fold01.p014 NMX_Fold01.p015 NMX_Fold01.p016 NMX_Fold01.p017 NMX_Fold01.p018 NMX_Fold01.p019 NMX_Fold01.p020 NMX_Fold02.p021 NMX_Fold02.p022 NMX_Fold02.p023 NMX_Fold02.p024 NMX_Fold02.p025 NMX_Fold02.p026 NMX_Fold02.p027 NMX_Fold02.p028 NMX_Fold02.p029 NMX_Fold02.p030 NMX_Fold03.p031 NMX_Fold03.p032 NMX_Fold03.p033 NMX_Fold03.p034 NMX_Fold03.p035 NMX_Fold03.p036 NMX_Fold03.p037 NMX_Fold03.p038 NMX_Fold03.p039 NMX_Fold03.p040 NMX_Fold04.p041 NMX_Fold04.p042 NMX_Fold04.p043 NMX_Fold04.p044 NMX_Fold04.p045 NMX_Fold04.p046 NMX_Fold04.p047 NMX_Fold04.p048 NMX_Fold04.p049 NMX_Fold04.p050 NMX_Fold05.p051 NMX_Fold05.p052 NMX_Fold05.p053 NMX_Fold05.p054 NMX_Fold05.p055
 rfl

def normalized (ops : Ops) (owners : Owners) (verifier : solana_pubkey.Pubkey)
 (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey)
 (outputLane : U8) (slot : U64) : Final :=
 if Slice.len accounts != 7#usize then
  if Slice.len accounts < 7#usize then ok (.Err .NotEnoughAccountKeys)
  else ok (.Err .InvalidArgument)
 else NMX_Fold00.v001 owners ops verifier accounts pool outputLane slot

theorem erased (ops : Ops) (owners : Owners) (verifier : solana_pubkey.Pubkey)
 (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey)
 (outputLane : U8) (slot : U64) :
 NMX_ValueLink.erase (eval (NMX_SourceModel.source ops owners)
  (NMX_SourceProgram.auth ops verifier accounts pool outputLane slot) ()) =
 normalized ops owners verifier accounts pool outputLane slot := by
 rw [source ops owners]
 unfold normalized
 rw [NMX_ControlLaws.eval_if]
 by_cases malformed : (Slice.len accounts != 7#usize) = true
 · simp only [malformed,↓reduceIte]
   rw [NMX_ControlLaws.eval_if]
   by_cases short : Slice.len accounts < 7#usize <;>
    simp only [short,↓reduceIte,eval,NMX_ValueLink.erase]
 · simp only [malformed,↓reduceIte]
   exact NMX_Fold00.e001 owners ops verifier accounts pool outputLane slot
#print axioms source
#print axioms erased
end NMX_FoldedProgram
end
