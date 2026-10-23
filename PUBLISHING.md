# GitHub Pages publication

This branch publishes a static snapshot of `main` commit
`b967a171ff4977e85b2a8493c9d7e5bfb1d087c6`, excluding the main-only `papers/` directory. GitHub Pages serves `gh-pages`
at `/` with HTTPS. The source repository remains private; the published
site is accessible by URL.

Every HTML page includes `noindex, nofollow, noarchive` robots metadata.
Crawling is allowed so search engines can read the indexing directives.
The in-page source-search controls remain available.

Tracked source and supporting files retain their relative paths. Downloaded
dependencies and attachments are excluded. Validation runs locally with
`bash scripts/check-local.sh` before publication. No project GitHub Actions
workflow files are included; Lean compilation and documentation checks run
locally, and GitHub Pages serves the generated static site.

To update the publication, start with the latest verified `main` snapshot and
reapply the indexing metadata to every HTML page before pushing `gh-pages`.
Do not regenerate HTML directly here without restoring those directives.

The `papers/` directory is never published. Apply documentation and cleanup commits
separately from paper-source commits; do not merge `main` wholesale into this
branch. Before publishing, `git ls-files papers` must return no files.

The kinetic Langevin and KIPLMC pages were approved for publication on
23 October 2026 with their documented source corrections and scope qualifications.
The local proof suite and 131 browser cases passed before publication.

The responsive diagram and automatic theme update was checked locally on
23 October 2026: 167 theme/layout cases, 65 connector and live-resize cases,
131 existing browser cases, and 49 code-copy cases passed. All documentation
checks passed. This update changes no Lean sources.
