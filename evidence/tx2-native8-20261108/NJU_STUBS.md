# NJU stubs

No field multiplication is run in Kani. Initial arbitrary-window decoder cuts use no arithmetic or child stubs. The only replacements are the exact KMX_copy_stubs.patch copy stubs, SHA256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67. Their existing KMX Lean value laws are retained; credit additionally requires a matched failing control. No function contract, stub_verified, writable static, observer or function-pointer assertion is used.

No new runtime trust. Native semantic transport remains option-A P6/D188 reclassification.

The generalized finish chain reuses the original NJF/NIW native G and its
Lean-discharged field laws; it creates no new multiplication stub. Inherited
NJR cuts and their unchanged paired theorem/domain inventory are pinned in
NJU_INHERITED_NATIVE_PINS.json. Caller-domain and cut association at the native
TX2:065 parent remains M01, not an assumed stub domain.
