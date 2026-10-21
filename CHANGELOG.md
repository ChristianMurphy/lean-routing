# Changelog

## [Unreleased]

- Add `decodedPath`, the decoded path segments that routes match a request against.
- Start a link or slash redirect whose first segment is empty with `/./`, so browsers keep it on the same host.
- `decodedPath` drops the `.` that such a link starts with.

## [0.10.1] - 2026-10-18

- Chore: bump dependencies.

## [0.10.0] - 2026-10-18

- Add `Router`, which groups routes and mounts behind per-subtree middleware.

## [0.9.0] - 2026-10-16

- A route pattern can no longer contain a `.` or `..` segment, since no link can reach one; `PathSeg.lit` takes a proof of this, so a match on it binds one more argument.
- Percent-encode literal segments in generated links.

## [0.8.0] - 2026-10-06

- Percent-encode `String` captures in generated links.
- A `String` capture no longer matches an empty, `.` or `..` segment, since no link can carry one.
- `relativeUrl` handles a trailing-slash current page, and a target segment that is empty or holds a `:`.
- A mounted index renders with a trailing slash, and a request for it without one is redirected there.
- Move to Lean v4.34.1.

## [0.7.2] - 2026-09-01

Expose the definitions a `route_table` generates, so a route table can be used from another module.

## [0.7.1] - 2026-08-29

Tidy the documentation, and fix an unterminated code fence in the README.

## [0.7.0] - 2026-08-20

Move to the module system, keeping the Lean frontend out of a consumer's binary.

## [0.6.0] - 2026-08-18

Add `matchedPattern?`

## [0.5.0] - 2026-08-16

Tidying up and restructuring

## [0.4.0] - 2026-08-13

Store matched route in both request and response.

## [0.3.0] - 2026-08-11

- Hierarchical handler construction
- Fit better with Lean idiomatic naming conventions

## [0.2.0] - 2026-08-03

Hierarchical routes

## [0.1.0] - 2026-07-17

Initial release
