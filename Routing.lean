/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Routing.Pattern
public import Routing.Handler
public import Routing.Route
public import Routing.Trie
public import Routing.Server
public import Routing.Router
public import Routing.RouteTable
public import Routing.RouteMount
public import Routing.RelativeLink

/-!
Low ceremony, with the static guarantee that a wrong-arity or wrong-type handler is a compile
error.

## Design overview

A route pattern string (`"/users/:id:Nat"`) parses (`Routing/Pattern.lean`) into `List PathSeg`,
plain runtime data with no type-level encoding. From that *value*, `HandlerType segs result`
(`Routing/Handler.lean`) computes the *type* a matching handler must have.

`Route`/`dispatchTable` (`Routing/Route.lean`) bundle a method, pattern, and handler into a table
tried in order. `matchTable` adds the identity of the route that matched, which `toHandler`
(`Routing/Server.lean`) publishes for a wrapping middleware to read back. `toHandler` and `Router`
find that route with a trie built once over the table (`Routing/Trie.lean`). It picks the route
`matchTable` would, without trying every one.

A `route_table` row can `mount` another table under a literal path prefix
(`Routing/RouteTable.lean`); `mount_routes` (`Routing/RouteMount.lean`) does the same for a list of
already-built routes. Either way an app composes from independently-declared feature modules, and
`Routing.relativeUrl` (`Routing/RelativeLink.lean`) lets code inside one self-link from its own
unprefixed links, wherever the module ends up mounted.

A `Router` (`Routing/Router.lean`) groups routes, and mounts of them, behind its own middleware,
and flattens them to the same `List (Route Result)` that `toHandler` serves.

## Limitations

- **Query-string parameters**: `dispatch` matches the path only.
- **`CaptureKind` is a closed enum** (`Nat`/`String` only), so downstream
  code cannot add capture types of its own.
- **Captured mount prefixes**: a `mount` prefix must be literal, so routes
  cannot be mounted under a prefix containing a `:name:Kind` capture (a
  per-tenant `/orgs/:orgId:Nat/...` prefix, for instance).
-/
