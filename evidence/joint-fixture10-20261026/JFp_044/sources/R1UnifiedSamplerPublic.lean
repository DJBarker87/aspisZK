import AspisV8R19.DuplexFrames
set_option autoImplicit false
namespace AspisR1.UnifiedSampler
open AspisV8R19.DuplexFrames
structure Public (L : Nat) where
  pubBytes : Bytes
  initFits : 75 + pubBytes.length ≤ L
  tag : Byte

#print axioms Public
end AspisR1.UnifiedSampler
