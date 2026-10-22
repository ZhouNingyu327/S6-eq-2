# Rebuild the English edition

See the root README for the build order. Node dependencies are pinned in
package.json. The renderer embeds math fonts into portable HTML and checks
formula parsing and local links. The combiner resolves named PDF targets and
checks that link annotations and module bookmarks survive merging. These
are document checks, not geometric proof checks.
