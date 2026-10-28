K004/K005: dynamic-length union, master <=385 bytes; no native credit.
K024: exact384-byte version-rejection domain with all remaining bytes arbitrary
also times out95.237s. This retires full-buffer master header attempts. Queue
validation now refuses later version/encoding/lane-count/depth master shapes
before admission; different invalid bytes are not a remedy for this failure.
The replacement is native one-window/one-iteration fragments and symbolic
reference composition. Unrelated checkpoint/lane members may still proceed.
No solver timeout increase or memory-cap increase is authorized.
K025 checkpoint and K026 lane correct-length version-rejection cases also
TIMEOUT. Full-buffer header cases are retired for all three decoders. A queued
encoding-master item was refused by this job's own preflight, before admission
or Kani submission; it consumes no Kani run and has no proof credit.
