# Reproducible target verification

Run `python3 lean/comparator/check-inputs.py` and
`python3 lean/comparator/check-fc-draft.py` from the repository root.
The workflow builds `lean/`, compares all five targets in `lean/comparator.json`,
audits the permitted axioms and replays the exported solution in the builtin Lean kernel.
The independent fresh replay job checks the entire FCSolution environment.

The version pins include the original proof commit, FC reference base, Mathlib,
Lean Comparator, Landrun and a Lean4export release matching Lean 4.35.0-rc3 exactly.
The trusted target depends only on Mathlib, uses fixed definitions without holes,
and is compiled before proof build products are restored in the checking job.

On Linux, set COMPARATOR_TOOLS to a new tool directory, run install-tools.sh,
then run-check.sh. GitHub Actions prepares the required tools and systemd sandbox.
For archiving a completed run, use archive-run.py with the exact repository,
run ID, attempt, expected tested commit and a new output directory.
