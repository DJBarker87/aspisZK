# PCI stubs

PCI_K003/K002: only core::ptr::copy_nonoverlapping -> exact KMX_copy_nonoverlapping, patch sha256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67. The note hash is the actual generic argument, not a function-pointer stub; its exact request and arbitrary reply are observed. No multiplication stub yet.
