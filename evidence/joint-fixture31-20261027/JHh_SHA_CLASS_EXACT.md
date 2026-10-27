# Exact fixture SHA interfaces

Existing JHe module is immutable. The accepted1 target uses ONLY its453 equations.
The new JHh extension adds only three retained-byte digest equations for the
writer identity route; no body/success/output identity is a field.

```lean
import JHe_SHAEquations0
import JHe_SHAEquations1
import JHe_SHAEquations2
set_option autoImplicit false
namespace AspisR1
/-- Exactly 453 concrete batch SHA equations as three finite law families. -/
class JHe_SHARealization : Prop where
  tree0 : ∀ i : Fin 157, JFp_SHADigest.digest (JHe_SHAInputs0.input i)=JHe_SHAInputs0.expected i
  tree1 : ∀ i : Fin 157, JFp_SHADigest.digest (JHe_SHAInputs1.input i)=JHe_SHAInputs1.expected i
  tree2 : ∀ i : Fin 139, JFp_SHADigest.digest (JHe_SHAInputs2.input i)=JHe_SHAInputs2.expected i
end AspisR1
```

```lean
import JHe_SHARealization
import JFn_HashBoundary
set_option autoImplicit false
namespace AspisR1
open AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
/-- The inherited 453 tree equations, plus three concrete retained-byte
requests. No success, output identity, or execution is a field. The immutable
JHe interface is extended here rather than edited. -/
class JHh_SHARealization : Prop extends JHe_SHARealization where
  proof : JFp_SHADigest.digest (flatten JFn_HashBoundary.proofParts)=decodeState JFo_AuthBytes.proofHash
  publicInput : JFp_SHADigest.digest (flatten JFn_HashBoundary.publicParts)=decodeState JFo_AuthBytes.publicHash
  checksum : JFp_SHADigest.digest (flatten JFn_HashBoundary.checksumParts)=decodeState JFo_AuthBytes.checksum
end AspisR1
```
