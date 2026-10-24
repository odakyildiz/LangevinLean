# GitHub Pages publication

This branch publishes a static snapshot of `main` commit
`bec1fcab11427227fc604a706a16c4a0e702f74c`, excluding the main-only `papers/` directory. GitHub Pages serves `gh-pages`
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

On 24 October 2026, the publication was synchronized with the restored `main`
snapshot. Its site and source files are unchanged from the previously verified
pre-AverageLMC publication; AverageLMC remains on `investigations`. The
main-only `papers/` directory remains excluded.

On 24 October 2026, the pages were redesigned to match the Latin Modern
typography and neutral/red palette of odakyildiz.com. The project index was
shortened while retaining source attribution and scope qualifications. Current
proof pages and standalone archives share the design, with fonts bundled locally.
Documentation integrity, responsive layouts, light/dark themes, reading controls,
and source search were checked locally. This update changes no Lean proofs.

Shared stylesheets and the theme script use content-based URL versions so
returning readers receive assets that match each updated page. This was checked
with the browser cache retained after deployment.
