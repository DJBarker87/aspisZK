# Own-input repairs

NJC_L001 prelaunch dependency pinning rejected nonexistent module NFN_NEO_TailReference. The declaration owner is NFN_GeometryPart05 per NIU row TX2:056. Corrected the import; no Lean process was submitted and no compiled attempt was rerun.

NJC_K001 stopped in own source validator BEFORE Cargo/Kani: predecessor pins included extra extraction-only tools outside the NHR staging manifest. Replaced the pin input with the exact frozen NHR manifest (all 666 staged release files), plus own cfg-only harness and exact KMX bytes. Validation remains complete for the staged corpus.

NJC_K002 graph/source checks passed; Rust codegen found cfg(kani) #[path] reference tree.rs outside the NHR production corpus. Added frozen tools/r1-builder-reference Rust inputs, hashed against the frozen revision; no production body change. This is an own-input missing-file repair, not a timed-out shape.

NJC_K003 Rust codegen rejected missing root imports for the exact KMX stubs. Added the predecessor-identical cfg(kani) include and allocator_api cfg attribute; stub files remain hash-identical to the supplied KMX patch. No Kani solver ran in K001–K003.
