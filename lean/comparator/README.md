# Reproducible target verification

Run `python3 lean/comparator/check-inputs.py` and
`python3 lean/comparator/check-fc-draft.py` from the repository root.
The workflow builds `lean/`, compares all five targets in `lean/comparator.json`,
audits the permitted axioms and replays the exported solution in the builtin Lean kernel.
The independent fresh replay job checks the entire FCSolution environment.

The version pins include the original proof commit, FC reference base, Mathlib,
Lean Comparator, Landrun and Lean4export. The proof, reference, Comparator and
Lean4export all build with Lean 4.33.1. The two checker tools are pinned to their
last 4.33 source revisions, with a recorded toolchain-only change from 4.33.0 to
4.33.1. Their Lean source code is unchanged.
The trusted target depends only on Mathlib, uses fixed definitions without holes,
and is compiled before proof build products are restored in the checking job.

On Linux, set COMPARATOR_TOOLS to a new tool directory, run install-tools.sh,
then run-check.sh. GitHub Actions prepares the required tools and systemd sandbox.
For archiving a completed run, use archive-run.py with the exact repository,
run ID, attempt, expected tested commit and a new output directory.
