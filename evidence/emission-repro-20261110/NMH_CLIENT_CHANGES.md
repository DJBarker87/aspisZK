# Owned extraction controller

NMH_NHR_stage.py is a byte-identical copy of NHR_stage.py, pinned in NMH_STAGER_PIN.json. NMH_extract.py imports it and supplies its options() result from archived command arrays. This avoids editing the fixed four-driver CLI, while every compiler call still happens in NHR extract(), after its staging/metadata/tool hash validation and before its final source/lock checks. No launcher/reservation/shim/shared workspace is changed. A separate GNU time wrapper records each tool's resources.

NMH_run.py derives from NHR_run.py: owned directory/prefix, mandatory disk admission before scope, quiet output, excludes LLBC and duplicate cargo metadata from text collection. All original reservation exit+allowed checks and serial SInt2 scope/timeout behavior remain. Sources/configuration arrays and transport payload are committed inputs. No local Rust/Lean compile occurs.

The frozen transport is NHR's payload with only programs/aspis-pool replaced directly from b936275465, as explicitly required by the owner amendment. Each replacement has its git blob, byte count, SHA256 and revision. Crates, verifier program, root manifest and lock remain 4bb3b3f. NHR's discovery and path-dependency validation are retained. Historical reference crates or outlined entry functions absent from that frozen source are not manufactured.

NMH_PLAN groups are conservative namespaces/packet configurations; run entries consolidate identical recovered exact command shapes and list all candidate groups. A candidate does not establish that every listed group came from it. Full-byte or allowed-normalization comparison decides that. No new normalization is authorized.
