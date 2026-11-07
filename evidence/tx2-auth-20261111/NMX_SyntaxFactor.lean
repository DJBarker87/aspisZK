import NMX_SF00
set_option autoImplicit false
noncomputable section
namespace NMX_SyntaxFactor
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Program
attribute [local instance] Classical.propDecidable
/-- Literal factorization only: no child definition, allocator or getter is unfolded. -/
theorem factor (verifier : solana_pubkey.Pubkey)
 (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey)
 (outputLane : U8) (slot : U64) :
 NMX_Skeleton.auth verifier accounts pool outputLane slot =
 if Slice.len accounts != 7#usize then
  if Slice.len accounts < 7#usize then .reject .NotEnoughAccountKeys else .reject .InvalidArgument
 else NMX_SF00.p001 verifier accounts pool outputLane slot := by
 unfold NMX_Skeleton.auth
 unfold NMX_SF00.p001 NMX_SF00.p002 NMX_SF00.p003 NMX_SF00.p004 NMX_SF00.p005 NMX_SF00.p006 NMX_SF00.p007 NMX_SF00.p008 NMX_SF00.p009 NMX_SF00.p010 NMX_SF01.p011 NMX_SF01.p012 NMX_SF01.p013 NMX_SF01.p014 NMX_SF01.p015 NMX_SF01.p016 NMX_SF01.p017 NMX_SF01.p018 NMX_SF01.p019 NMX_SF01.p020 NMX_SF02.p021 NMX_SF02.p022 NMX_SF02.p023 NMX_SF02.p024 NMX_SF02.p025 NMX_SF02.p026 NMX_SF02.p027 NMX_SF02.p028 NMX_SF02.p029 NMX_SF02.p030 NMX_SF03.p031 NMX_SF03.p032 NMX_SF03.p033 NMX_SF03.p034 NMX_SF03.p035 NMX_SF03.p036 NMX_SF03.p037 NMX_SF03.p038 NMX_SF03.p039 NMX_SF03.p040 NMX_SF04.p041 NMX_SF04.p042 NMX_SF04.p043 NMX_SF04.p044 NMX_SF04.p045 NMX_SF04.p046 NMX_SF04.p047 NMX_SF04.p048 NMX_SF04.p049 NMX_SF04.p050 NMX_SF05.p051 NMX_SF05.p052 NMX_SF05.p053 NMX_SF05.p054 NMX_SF05.p055
 rfl
#print axioms factor
end NMX_SyntaxFactor
end
