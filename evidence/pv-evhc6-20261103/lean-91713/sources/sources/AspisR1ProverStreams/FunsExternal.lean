import AspisR1ProverStreams.Types
open Aeneas Aeneas.Std Result
namespace AspisR1ProverStreams
def aspis_core.field.P : Result U32 := ok 2147483647#u32
/-! Drop methods are unsupported, rather than axiomatized. They are not called
by the sampler/next-word address theorem. -/
def zeroize.Zeroize.Blanket.zeroize {Z : Type}
    (_inst : zeroize.DefaultIsZeroes Z) (_self : Z) : Result Z := .fail .panic

def Array.Insts.ZeroizeZeroize.zeroize {Z : Type} {N : Usize}
    (_inst : zeroize.Zeroize Z) (_self : Array Z N) : Result (Array Z N) := .fail .panic

def zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref {Z : Type}
    (_inst : zeroize.Zeroize Z) (self : zeroize.Zeroizing Z) : Result Z := ok self
end AspisR1ProverStreams
