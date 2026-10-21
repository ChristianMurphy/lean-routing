#!/usr/bin/env bash
# Copyright (c) 2026 Paul Butcher. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Nothing from the Lean package may reach a consumer's binary, `route_table` and `mount_routes`
# included. `check-imports.sh` reads that claim off the library's source; this one reads it off
# an executable that actually uses both macros, which is the form the claim is about.
#
# `test/LeanFree.lean` is that executable. Building it builds the library too, so everything
# examined below is this checkout's own output rather than whatever was lying around.
#
# Note that the link line is not the place to look: Lake names `-lLean` for every executable it
# builds, whether or not anything needs it, and a library archive contributes only the members
# something referred to. What ended up in the binary is the answer.

set -euo pipefail

cd "$(dirname "$0")/.."

command -v nm >/dev/null || { echo "error: 'nm' is needed to read the binary's symbols" >&2; exit 1; }

# One `lake` at a time: this script is also run from the root package's test driver.
(cd test && lake build leanFree >/dev/null)

exe=test/.lake/build/bin/leanFree
status=0

# `grep -c` rather than `grep -q`, and a count rather than an exit status: `-q` stops at the first
# match and so kills the process feeding it, which under `pipefail` reads as "found nothing".
# Module initialisers name the package; ordinary symbols name only the namespace, and core `Init`
# declares things in `Lean.Elab` too, some of whose storage AArch64 links into every binary.
frontend_hits() { grep -c 'initialize_Lean_' || true; }

# 1. No compiled module of the library starts a Lean module at run time. Its *meta* initialiser
#    does, which is the whole point of a `meta import`: the elaborator gets the frontend, and a
#    program that merely routes requests does not.
for c in .lake/build/ir/Routing.c .lake/build/ir/Routing/*.c; do
  [ -f "$c" ] || continue
  if [ "$(awk '/LEAN_EXPORT lean_object\* runtime_initialize_/,/^}/' "$c" | frontend_hits)" -ne 0 ]; then
    echo "error: $c starts a Lean module at run time, not only during elaboration" >&2
    status=1
  fi
done

# 2. The consumer's own compiled module, the one holding what `route_table` generated, refers to
#    nothing from the Lean package.
if [ "$(frontend_hits < test/.lake/build/ir/LeanFree.c)" -ne 0 ]; then
  echo "error: the consumer's compiled module refers to the Lean package" >&2
  status=1
fi

# 3. Neither does the executable those modules were linked into.
if [ "$(nm "$exe" | frontend_hits)" -ne 0 ]; then
  echo "error: $exe carries Lean frontend symbols" >&2
  status=1
fi

# 4. And it still routes. A binary that cannot route is a cheap way to pass 1-3.
expected="user 7
post hi
no match
/blog/
/blog/posts/hi
/users/7"
actual=$("./$exe")
if [ "$actual" != "$expected" ]; then
  echo "error: $exe did not route as expected; got:" >&2
  echo "$actual" >&2
  status=1
fi

if [ "$status" -eq 0 ]; then
  echo "ok: an executable using both macros carries nothing from the Lean package ($(du -h "$exe" | cut -f1))"
fi
exit "$status"
