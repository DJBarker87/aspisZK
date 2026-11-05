# NIC stub inventory

Runtime frontier: SolanaDigest::digest, solana_program::hash::hashv, program::{set_return_data,get_return_data,invoke,invoke_signed}, log::{sol_log,sol_log_compute_units}: every replacement asserts unreachability. Activation controls K002/K021–K027 verify the mappings, not runtime values.

M31::mul -> m31_product_spec: kani::any u32 constrained to ((a as u64)*(b as u64)) % 2147483647. Paired named law AspisR1.NFP_ProductLaw.emitted (all U32 inputs, exact ok result and natural value); native value law reused, not replayed. No native multiplication is verified.

WideExact::mul / mul_m31 candidates in K028 are excluded after TIMEOUT. Their exact natural-spec association still needs paired law review; no pass is booked for either.

KMX copy_nonoverlapping uses the exact unmodified KMX_copy_stubs.patch, SHA256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67. K017/K018 calibrate positive/inverted-copy controls. KMX value/frame laws remain KMX_CopyMeaning.

RuntimeSyscall returningValue (no totality), allocator/Std/compiler/ABI/Aeneas/source-to-ELF and P6/D188 option-A semantic transport remain explicit. No runtime trust row is added or removed.
