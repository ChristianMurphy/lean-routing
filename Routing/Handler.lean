/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Routing.Pattern
public import Std.Http.Data.URI.Encoding

public section

@[expose] section

namespace Routing

/-- One argument per capture in `segs`, in order, correctly typed via `CaptureKind.type`;
literal segments contribute nothing. -/
def HandlerType (segs : List PathSeg) (result : Type) : Type :=
  match segs with
  | [] => result
  | .lit _ :: rest => HandlerType rest result
  | .capture _ kind :: rest => kind.type → HandlerType rest result

/-- The `String` captures no link can carry as one path segment: a client removes dot segments, even
percent-encoded ones, before sending a request, and an empty one is collapsed by many proxies and, as
the last segment, cannot be told from a trailing slash. -/
def unlinkable (s : String) : Bool :=
  s == "" || s == "." || s == ".."

/-- Matches a decoded request path (`List String`, e.g. from
`RequestTarget.path.toDecodedSegments`) against `segs`, applying `handler`
to the extracted, typed capture values as it goes.

A trailing `""` once `segs` is exhausted matches too: `Std.Http`'s path parser appends an empty
segment for a request path ending in `/` (e.g. `/todos/7/` decodes to `["todos", "7", ""]`), and a
route's own pattern never has a trailing slash of its own to match it structurally. Tolerating it
here means a directory-style relative reference (e.g. `Routing.relativeUrl`'s `"."`/`".."` case,
which an RFC 3986-compliant resolver always turns into a trailing-slash URL) actually reaches its
target instead of 404ing.

A `.string` capture never matches an `unlinkable` segment, so a capture always has a working link. -/
def dispatch {result : Type} :
    (segs : List PathSeg) → HandlerType segs result → List String → Option result
  | [], h, [] => some h
  | [], h, [""] => some h
  | .lit s :: rest, h, p :: ps => if s == p then dispatch rest h ps else none
  | .capture _ .nat :: rest, h, p :: ps => p.toNat?.bind (fun n => dispatch rest (h n) ps)
  | .capture _ .string :: rest, h, p :: ps =>
    if unlinkable p then none else dispatch rest (h p) ps
  | _, _, _ => none

/-- `String` for a pattern with no captures; otherwise one argument per capture, in order,
returning the rendered path. -/
@[reducible] def LinkType : List PathSeg → Type
  | [] => String
  | .lit _ :: rest => LinkType rest
  | .capture _ kind :: rest => kind.type → LinkType rest

/-- Builds the `/`-joined path for `segs`, given the literal/rendered-capture parts collected so
far. A `.string` capture is percent-encoded, so the link dispatches back to it unless it is
`unlinkable`. -/
def linkParts : (segs : List PathSeg) → List String → LinkType segs
  | [], parts => "/" ++ String.intercalate "/" parts
  | .lit s :: rest, parts => linkParts rest (parts ++ [s])
  | .capture _ .nat :: rest, parts => fun n => linkParts rest (parts ++ [toString n])
  | .capture _ .string :: rest, parts => fun s =>
    linkParts rest (parts ++ [toString (Std.Http.URI.EncodedSegment.encode s)])

/-- The reverse-routing function for a route pattern's segments: a `String`, or a function taking
one argument per capture (in order) and returning one, e.g.
`linkFor [.lit "todos", .capture "id" .nat] : Nat → String`. -/
def linkFor (segs : List PathSeg) : LinkType segs := linkParts segs []

end Routing
