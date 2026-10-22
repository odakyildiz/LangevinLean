# GitHub Pages publication

This branch publishes a static snapshot of `main` commit
`89d9f7adb2b6e3e746ad15c1061a3555c6839f3c`. GitHub Pages serves `gh-pages`
at `/` with HTTPS. The source repository remains private; the published
site is accessible by URL.

Every HTML page includes `noindex, nofollow, noarchive` robots metadata.
Crawling is allowed so search engines can read the indexing directives.
The in-page source-search controls remain available.

Tracked source and supporting files retain their relative paths. Downloaded
dependencies and attachments are excluded. The source branch’s CI workflows
are omitted from this deployment branch.

To update the publication, start with the latest verified `main` snapshot and
reapply the indexing metadata to every HTML page before pushing `gh-pages`.
Do not regenerate HTML directly here without restoring those directives.
