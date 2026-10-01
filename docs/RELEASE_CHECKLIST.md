# Release checklist

This checklist distinguishes verified proof artifacts from publication
decisions. It is not a claim of independent peer review or institutional
endorsement. Run the checks on the exact source revision being released.

## Proof and artifact checks

- Run `lean/check.sh` successfully and retain the source fingerprint and
  axiom report. The only permitted proof axioms are `propext`,
  `Classical.choice`, and `Quot.sound`.
- Validate `formalization.yaml`, manuscript labels, declaration mappings,
  challenge configurations, copyright headers, and the manuscript checksum.
- Build and check an exported source tree without the working directory's
  cached package symlinks. Record the actual outcome.
- Reproduce the separate local Comparator and Nanoda checks using the README
  commands; retain their source-bound outcomes and distinct execution modes.
- Run the Comparator challenges in a supported Linux sandbox with the
  pinned independent-checker tools. Keep this verdict separate from ordinary
  Lean compilation and any unsandboxed local diagnostic.
- Confirm the manuscript-to-Lean correspondence with an independent human
  reviewer. Record the reviewer's name and scope only after review occurs.

## Publication record and remaining metadata

The maintainer explicitly requested publication to
[JWang226/QMDL](https://github.com/JWang226/QMDL), including the reproduction
commands. The repository URL is recorded in `CITATION.cff` and
`formalization.yaml`. Its existing wiki and deployment workflow are retained.
Publishing the source does not turn pending review or licensing decisions
into completed checks.

- Confirm the copyright-holder names and public-release license. The
  current choice is recorded in `LICENSE`; a pending choice is not a grant.
- Complete the prior-formalization attribution and license record for the
  two adapted modules listed in `NOTICE`.
- Confirm distribution rights for the manuscript and any optional PDF, and
  retain the original notices in the bundled TeX support files.
- Keep the actual GitHub URL and exact reproduction commit in citations.
  Do not insert a guessed DOI.
- Choose a version/tag and an appropriate scholarly archive or persistent
  identifier. Keep the paper and formalization versions linked.
- Replace unavailable model/cost/provenance fields only with reliable data.
  Do not relabel an agent review as human verification.

## Prepare the release tree

Use the explicit allowlist exporter described in `REPRODUCIBILITY.md`.
Inspect the generated manifest and ensure no `.lake`, credentials, local
paths, unrelated drafts, generated TeX logs, or machine-specific build
products are included. The optional existing PDF must be selected
explicitly. Initialize or push a Git repository only when publication is
separately requested.
