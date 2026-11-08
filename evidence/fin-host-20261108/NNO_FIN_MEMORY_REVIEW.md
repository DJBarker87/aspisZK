FIN memory inspection

NNO_L015 FIN_240 exited 0 in 23.07 s, GNU time peak RSS 6804692 KiB,
swap 0. The draft FIN input already imports the real NMX and Aeneas closures;
NVR_Carrier had 4396912 KiB RSS, and NVR_NNCWeak had 6721972 KiB RSS while
cgroup memory.peak was only 699076608 bytes. This is a large mapped/imported
object closure, not growth from evaluating the one-fold proof.

The first job-owned pause guard watched lake instead of its Lean child, so it
did not pause L015 (or the already submitted L016). This is a validation-script
finding. The guard is repaired to inspect the whole child tree, pause the
largest child above 1 GiB RSS, retain /proc/status and object mapping records,
and resume that same process only if anonymous memory is below 1 GiB and the
excess is predominantly file-backed. Otherwise it stops the process. Caps and
180 s limit are unchanged. No successful compile is repeated to hide this gap;
L015/L016 resource inspection is retrospective, explicitly distinguished from
the remaining live inspections. The formal theorem/axiom results are separate.
