# GitHub Pages publication

This branch publishes a static snapshot of `main` commit
`eaa9fdcd316aaa67d9a6210921981f8300f394ed`. GitHub Pages serves `gh-pages`
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
