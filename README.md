# Routing

A typed HTTP router for Lean 4 / [`Std.Http`](https://leanprover-community.github.io/mathlib4_docs/Std/Http.html). Route patterns like `"/users/:id:Nat"` determine the exact type your handler must have; a wrong-arity or wrong-type handler is a compile error, not a runtime bug.

See: [Formally verified CRUD](https://paulbutcher.com/lean2.html).

## Installation

Add to your `lakefile.toml`:

```toml
[[require]]
name = "routing"
git = "https://github.com/paulbutcher/lean-routing.git"
```

## Usage

### 1. Declare your routes

```lean
import Routing

route_table AppName
  [ index := "/",
    user := "/users/:id:Nat",
    userPost := "/users/:id:Nat/posts/:slug:String" ]
```

This is a macro which parses the route specifications and generates `AppName.patterns` (the parsed patterns, for step 2) and `AppName.links` (link-building functions, described below).

### 2. Combine route handlers into an application

```lean
import Std.Http.Server
import Routing

open Std Http Server
open Routing
open AppName

def app : StatelessHandler := [
    .get patterns.index (fun request => Response.ok.text "home"),
    .get patterns.user (fun (id : Nat) request => Response.ok.text s!"user #{id}"),
    .post patterns.userPost (fun (id : Nat) (slug : String) request => Response.ok.text s!"user #{id}, post {slug}")
  ] |> toHandler
```

Unmatched requests get a default `404 Not Found`; pass `notFound := ...` to `toHandler` to override it.

### 3. Wire into a server

```lean
def main : IO Unit := do
  ... Std.Http.Server.run app ...
```

### Generating links

Use `AppName.links.<name>` anywhere you need a URL for one of your routes, e.g. in a template:

```lean
#eval AppName.links.index       -- "/"
#eval AppName.links.user 42     -- "/users/42"
```

`AppName.links.user` is a function (`Nat → String`) because its pattern has one capture; a pattern with no captures gives a plain `String`. A `String` capture is percent-encoded, so `AppName.links.userPost 1 "a b/c"` is `"/users/1/posts/a%20b%2Fc"`, which dispatches back to `"a b/c"`. No link can carry an empty, `.` or `..` capture, so a `String` capture never matches one; validate such values (usernames, say) where they are created.

### Hierarchical routes

A `route_table` can `mount` another `route_table`-generated table under a literal path prefix, nesting its whole `patterns`/`links` shape:

```lean
route_table Blog
  [ index := "/",
    post  := "/:slug:String" ]

route_table AppName
  [ index := "/",
    blog  := mount "/blog" Blog ]
```

```lean
#eval AppName.links.blog.index        -- "/blog/"
#eval AppName.links.blog.post "hi"    -- "/blog/hi"
```

`AppName.patterns.blog.post` is the full prefixed pattern, so it plugs into `Route.get`/etc. the same way any other pattern does, and a handler for it needs no special wrapping: a mount prefix must be literal (no `:name:Kind` captures), so it never changes a route's required handler type. Mounts nest to any depth: a table that itself mounts other tables can be mounted again further up.

A mounted index renders with a trailing slash, as the unmounted index `/` has, so that relative links from it work (see "Relative links" below). A request for it without the slash gets a `308` redirect to the slashed form.

### Hierarchical handlers

`mount_routes "prefix" routes` is the handler-level counterpart: it takes a `List (Route _)` built against a sub-app's own *unprefixed* patterns and re-targets it under a literal prefix, so a module's handlers can be written once and mounted anywhere:

```lean
def blogRoutes : List (Route Result) :=
  [ .get Blog.patterns.index (fun request => Response.ok.text "blog home"),
    .get Blog.patterns.post (fun (slug : String) request => Response.ok.text s!"post {slug}") ]

def app : StatelessHandler :=
  ( [ .get AppName.patterns.index (fun request => Response.ok.text "home") ] ++
    mount_routes "/blog" blogRoutes
  ) |> toHandler
```

Like `mount`, no handler wrapping is needed for the prefix. Unlike `mount`, nesting is just repeated `mount_routes` + `++`; routes are already a flat list, so there's no structure to walk.

### Which route matched?

The matched route is stored in the `extensions` of both the request and the response. Read it back with `Routing.matchedRoute?`:

```lean
def handler (request : Request Body.Stream) : ContextAsync (Response Body.Any) := do
  let response ← inner request
  match Routing.matchedRoute? response.extensions with
  | some matched => ...   -- matched.segs = [.lit "users", .capture "id" .nat]
  | none => ...           -- nothing matched; this is the 404
```

Alternatively, `Routing.matchedPattern?` drops each capture's kind (useful for telemetry):

```lean
#eval Routing.matchedPattern? response.extensions  -- some "/users/:id", not "/users/:id:Nat"
```

### Relative links

`Routing.relativeUrl current to` builds a relative reference between two already-rendered links, so code inside a module can self-link using its own *unprefixed* `.links`, with no need to know whether, or under what prefix, the module ends up mounted:

```lean
#eval Routing.relativeUrl Blog.links.index (Blog.links.post "hi")  -- "hi"
```

This comes out the same whichever prefix `Blog` is mounted under (or none at all), because a prefix shared by both endpoints cancels out of the computation:

```lean
#eval Routing.relativeUrl AppName.links.blog.index (AppName.links.blog.post "hi")  -- "hi", too
```

Linking to a strict descendant of the current page needs its own segment repeated (`relativeUrl "/posts/5" "/posts/5/edit" = "5/edit"`, not `"edit"`); that is the standard RFC 3986 rule that treats the current page's last segment as a "file", not a directory. Linking *up* to an ancestor page renders as a directory reference (`"."`/`".."`), which resolves to a trailing-slash URL; `dispatch` tolerates that trailing slash once a pattern is otherwise fully matched, so the link still reaches its target.

## License

This library is released under the Apache 2.0 license. See the LICENSE file for the complete license text.
