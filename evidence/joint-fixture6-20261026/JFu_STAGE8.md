# Stage 8: real public metadata reads and indices

JFu_PublicMeta00–08 independently check the real late/snapshot/afterstate/
payment header windows, pool/domain bindings, two snapshot index fields and fee
bytes. Each includes an emitted source range-read equation from public1880.
JFu_PublicIndices proves both snapshot indices decode to13 and afterstate index
to14, with the actual checked-add transition. These are actual selected bytes;
complete parent decoding/validation has not been inferred from them.

The metadata generator --check passes after explicit scalar normalization was
added following088. No maxRecDepth option or unchanged retry was used.
