# NLF native stubs

No field multiplication stub, digest/SHA stub, writable static, Option<fn>
observer, raw guard fabrication, or Ref/RefMut stub_verified use occurs.

| Stub | Exact replacement / Lean value law | Domain / controls |
|---|---|---|
| core::ptr::copy_nonoverlapping | Canonical KMX_copy_nonoverlapping from the EXACT KMX patch; KMX_CopyMeaning.loop_spec / copy_frame | Valid initialized source and exclusive destination, nonoverlap, in-bounds count; actual safely constructed typed carriers; K005 PASS / K006 FAIL |
| <[u8]>::copy_from_slice (K044/K045) | Canonical KMX_copy_from_slice; KMX_CopyMeaning.loop_spec; NLF_CopyValue.copy_coordinate/copy_frame/copy_whole | One-byte source/destination window at an arbitrary CP offset, typed exclusive guard, equal window lengths; K044 PASS / K045 FAIL |
| stub_verified(shape_effect) | Calibration ONLY on ScalarReply {value:u64,tag:u8}; K054 checks actual effect contract | K050 real body PASS, K052 unimplied caller assertions FAIL; inverse K049 FAIL and modifies K053 detected. Never used to substitute an SDK operation in an admitted support law |

Patch sha256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67.
No custom copy replacement was written. Ordinary native primitive calls execute
inside the harness; all call logs, guard variables and counters are local.
