# PIN2 ELF rebuild (S3, provisional)

sha256 (first):
- r1-cost-probe default: 5f083ab38e4b5bbe023bffda603a26aa969019a700cb194114625ec448ff6f7f
- r1-cost-probe retarget: 2284239edf238730aa0def62ec06176c364f6cb35cef1934ca18b0df0fbd6278
- aspis-upload: 9b2ab3d41695d81bfb79b93931d9323515fcc28a35fd725253be5e41bdc45874

Built from git archive of pin c7593d23fdc. All exit 0, offline, Cargo.lock unchanged. Default vs retarget differ in 63 bytes within one 64-byte span (offsets 1530537..1530600). Details in PIN2_ELF.json and elf_receipts/. Rerun for the final head: extract the archive into a new src dir (host workspace) and bash PCXS_elf_driver.sh.
