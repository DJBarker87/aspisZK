import NMX_R2_CB00
import NMX_R2_RSNormalize
set_option autoImplicit false
namespace NMX_R2_CanonicalBodyFactor
open RSL
/-- Both sides are canonical typed reference programs. Every child and
allocation remains folded; this is not the native observation interpretation. -/
theorem factor (L : PoolLib) (D : DeployedIds) (verifier pool : B32)
 (outputLane : UInt8) (slot : UInt64) (p m c l r e v : OwnedAccount) :
 NMX_R2_CB00.r008 L D verifier pool outputLane slot p m c l r e v =
 TX2_233.body L D ⟨verifier,[p,m,c,l,r,e,v],pool,outputLane,slot⟩ p m c l r e v := by
 unfold NMX_R2_CB00.r008 NMX_R2_CB00.r009 NMX_R2_CB00.r010 NMX_R2_CB01.r011 NMX_R2_CB01.r012 NMX_R2_CB01.r013 NMX_R2_CB01.r014 NMX_R2_CB01.r015 NMX_R2_CB01.r016 NMX_R2_CB01.r017 NMX_R2_CB01.r018 NMX_R2_CB01.r019 NMX_R2_CB01.r020 NMX_R2_CB02.r021 NMX_R2_CB02.r022 NMX_R2_CB02.r023 NMX_R2_CB02.r024 NMX_R2_CB02.r025 NMX_R2_CB02.r026 NMX_R2_CB02.r027 NMX_R2_CB02.r028 NMX_R2_CB02.r029 NMX_R2_CB02.r030 NMX_R2_CB03.r031 NMX_R2_CB03.r032 NMX_R2_CB03.r033 NMX_R2_CB03.r034 NMX_R2_CB03.r035 NMX_R2_CB03.r036 NMX_R2_CB03.r037 NMX_R2_CB03.r038 NMX_R2_CB03.r039 NMX_R2_CB03.r040 NMX_R2_CB04.r041 NMX_R2_CB04.r042 NMX_R2_CB04.r043 NMX_R2_CB04.r044 NMX_R2_CB04.r045 NMX_R2_CB04.r046 NMX_R2_CB04.r047 NMX_R2_CB04.r048 NMX_R2_CB04.r049 NMX_R2_CB04.r050 NMX_R2_CB05.r051 NMX_R2_CB05.r052 NMX_R2_CB05.r053 NMX_R2_CB05.r054 NMX_R2_CB05.r055 TX2_233.body
 simp only [RS.bind_pure,RS.seq,NMX_R2_SpecAssociativity.rust,
  NMX_R2_RSNormalize.bind_if,NMX_R2_RSNormalize.check_bind,RS.bind_throw,
  NMX_R2_RSNormalize.condition_or]
#print axioms factor
end NMX_R2_CanonicalBodyFactor
