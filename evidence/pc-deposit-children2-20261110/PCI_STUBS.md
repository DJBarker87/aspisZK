# PCI stubs

PCI_K003/K002: only core::ptr::copy_nonoverlapping -> exact KMX_copy_nonoverlapping, patch sha256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67. The note hash is the actual generic argument, not a function-pointer stub; its exact request and arbitrary reply are observed. No multiplication stub yet.

Planned POOL:223: M31::mul -> product_spec, both inputs <P asserted at the actual invocation, output arbitrary constrained to ((a as u64)*(b as u64))%P and <P. Paired theorem PCI_Mul.value derives emitted ok/value/canonicality from the existing CLOSED probe equality. No pass credited until L006 and native prefix/one-step/fold pass. Canonical-digest cut must consume CLOSED POOL:224 at SAME digest; its spec is eight raw-limb range checks and its perturbed-spec control is PCI_K017.
