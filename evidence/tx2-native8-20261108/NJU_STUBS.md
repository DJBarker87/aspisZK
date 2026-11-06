# NJU stubs

No field multiplication is run in Kani. Initial arbitrary-window decoder cuts use no arithmetic or child stubs. The only replacements are the exact KMX_copy_stubs.patch copy stubs, SHA256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67. Their existing KMX Lean value laws are retained; credit additionally requires a matched failing control. No function contract, stub_verified, writable static, observer or function-pointer assertion is used.

No new runtime trust. Native semantic transport remains option-A P6/D188 reclassification.
