/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Routing.RouteTable
import Routing.Route

namespace Routing

route_table RouteTableTest
  [ index := "/",
    active := "/active",
    edit := "/todos/:id:Nat/edit" ]

#guard RouteTableTest.patterns.index = []
#guard RouteTableTest.patterns.active = [.lit "active"]
#guard RouteTableTest.patterns.edit = [.lit "todos", .capture "id" .nat, .lit "edit"]
#guard RouteTableTest.links.index = "/"
#guard RouteTableTest.links.active = "/active"
#guard RouteTableTest.links.edit 7 = "/todos/7/edit"

-- A route built from `App.patterns` needs no pattern-string parsing of its own; `HandlerType`
-- is computed straight from the already-parsed segments.
private def editRoute : Route String :=
  .get RouteTableTest.patterns.edit (handler := fun (id : Nat) => s!"edit #{id}")

#guard dispatchTable [editRoute] .get ["todos", "7", "edit"] = some "edit #7"
#guard dispatchTable [editRoute] .get ["todos", "notanumber", "edit"] = none

-- Negative-compile regression: declaring the same name twice is a command-time error, not a
-- silently-overwritten field.
/--
error: route name 'index' already declared at `index
-/
#guard_msgs in
route_table RouteTableTestDup
  [ index := "/",
    index := "/elsewhere" ]

-- Negative-compile regression: a malformed pattern string is a command-time error at the row
-- that declares it (`segsSrcFor`, `RouteTable.lean`), not a silently-accepted bad route.
/--
error: invalid route pattern "not-a-valid-pattern"
-/
#guard_msgs in
route_table RouteTableTestInvalid
  [ bad := "not-a-valid-pattern" ]

-- A printed table keeps one row per line, with spaces around `:=`, so formatters built on Lean's
-- pretty-printer leave tables readable.
section
open Lean Elab Command

/--
info: route_table App [index := "/",
    user := "/users/:id:Nat",
    api := mount "/api" Api]
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let src := "route_table App [ index := \"/\", user := \"/users/:id:Nat\", " ++
    "api := mount \"/api\" Api ]"
  let .ok stx := Parser.runParserCategory (← getEnv) `command src | throwError "parse failed"
  logInfo (← liftCoreM <| PrettyPrinter.ppCommand ⟨stx⟩)

end

end Routing
