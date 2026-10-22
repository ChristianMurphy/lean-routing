/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Routing.Handler
public meta import Routing.Pattern
public meta import Lean.Elab.Command
meta import Lean.Structure
meta import Std.Data.HashMap

/-!
`route_table App [ name := "pattern", ... ]`: generates, for each row, a field of a generated
`App.Patterns` structure (`List Routing.PathSeg`, the parsed pattern) and the corresponding field
of `App.patterns`, and a field of a generated `App.Links` structure (`Routing.LinkType` of the
parsed pattern; `Handler.lean`) and the corresponding field of `App.links` (built with
`Routing.linkFor`).

Every pattern is parsed exactly once, right here, at the `route_table` row that declares it, so
a malformed pattern is a compile error at that row. `App.patterns`, consumed directly by
`Route.get`/`.post`/etc. (`Route.lean`), is how a route built from this table avoids re-parsing
(and so re-validating) the same pattern string a second time. Both values are exposed: their
bodies are the interface, since `HandlerType`/`LinkType` reduce the pattern they are given, so a
module that builds a route from a table declared elsewhere needs more than the type.

A row can also *mount* another `route_table`-generated app under a literal path prefix
(`name := mount "prefix" SubApp`), nesting `SubApp`'s whole `Patterns`/`Links` shape,
recursively, to whatever depth `SubApp` itself mounts further apps, under `App.patterns.name`/
`App.links.name`. Prefixes must be literal (no `:name:Kind` captures): `HandlerType`/`LinkType`
only add a function arrow for `.capture` segments, so a literal prefix leaves a mounted route's
required handler type unchanged from what it would be for the un-mounted pattern, so no glue code
is needed at the call site that builds the actual `Route`.

Every `Patterns` and `Links` also carries `mountedAt`, the full prefix its table is mounted under,
and `Patterns` coerces to the `MountPoint` a `Router` mount takes (`Router.lean`).

The elaborator below is the only thing here that needs the Lean frontend, and it reaches it
through `meta import` alone, so a program built against this library does not link it
(`scripts/check-runtime.sh`).
-/

public section

namespace Routing

open Lean Lean.Elab Lean.Elab.Command

declare_syntax_cat routeTableRow
syntax ident " := " str : routeTableRow
syntax ident " := " "mount " str ppSpace ident : routeTableRow

/-- Factored out into its own named parser, rather than inlined into `routeTableCmd` below, because
the `,*,?` trailing-comma sugar only elaborates inside a `syntax name := ...` alias. Same shape core
uses for `rwRuleSeq` (`Init/Tactics.lean`). The sugar is spelled out as `sepBy` so that a printed
table puts each row on its own line. -/
syntax routeTableRows :=
  "[" ppIndent(withoutPosition(sepBy(routeTableRow, ",", ", " ppLine, allowTrailingSep))) "]"

/-- See the module docstring. `App` names the generated `App.Patterns`/`App.patterns`/
`App.Links`/`App.links` declarations. -/
syntax (name := routeTableCmd) "route_table " ident ppSpace routeTableRows : command

/-- A row is either a plain pattern (`.leaf`) or a mount of another app's whole table under a
literal prefix (`.mount`). -/
private meta inductive RowKind where
  | leaf (pat : TSyntax `str)
  | mount (prefixPat : TSyntax `str) (sub : Ident)

private meta def qualifyPlain (src : Syntax) (appName : Name) (suffix : Name) : Ident :=
  mkIdentFrom src (appName ++ suffix)

/-- Parses `src` as a `command` and elaborates it, blaming `ref` (the `route_table` invocation) on
a parse failure. See the "3/4" comment below for why generated commands go through source text
rather than `Syntax` quotation here. -/
private meta def elabCommandFromSource (ref : Syntax) (src : String) : CommandElabM Unit := do
  match Lean.Parser.runParserCategory (← getEnv) `command src with
  | .error msg => throwErrorAt ref msg
  | .ok stx => elabCommand stx

/-- `"@[expose] "` where that attribute is meaningful and not already implied, `""` otherwise:
Lean warns about it outside a `module` file, on a definition that is not public, and inside an
`@[expose] section`. Why the generated values are exposed at all: see the module docstring. -/
private meta def exposeSrc : CommandElabM String := do
  let scope ← getScope
  let inExposeSection := scope.attrs.any (· matches `(Lean.Parser.Term.attrInstance| expose))
  if (← getEnv).header.isModule && scope.isPublic && !inExposeSection then
    return "@[expose] "
  else
    return ""

/-- Lean *source text* for one already-parsed `PathSeg`, e.g. `.lit "todos"` renders as
`Routing.PathSeg.lit "todos"`. Used (below) to splice an already-parsed, already-in-normal-form
`List PathSeg` *literal* into generated code, rather than a pattern-string call the elaborator
would still have to reduce. -/
private meta def segSrc : PathSeg → String
  | .lit s _ => s!"Routing.PathSeg.lit {s.quote}"
  | .capture name .nat => s!"Routing.PathSeg.capture {name.quote} .nat"
  | .capture name .string => s!"Routing.PathSeg.capture {name.quote} .string"

/-- Parses `pat`'s string value with the real `Routing.parsePattern`, so what a `route_table` row
accepts can never drift from what `dispatch` itself accepts. -/
private meta def parseSegsOrThrow (pat : TSyntax `str) : CommandElabM (List PathSeg) :=
  match parsePattern pat.getString with
  | some segs => pure segs
  | none => throwErrorAt pat s!"invalid route pattern {pat.getString.quote}"

/-- Renders already-parsed segments back to Lean source text for a `List PathSeg` literal. -/
private meta def segsListSrc (segs : List PathSeg) : String :=
  "[" ++ String.intercalate ", " (segs.map segSrc) ++ "]"

private meta def segsSrcFor (pat : TSyntax `str) : CommandElabM String :=
  return segsListSrc (← parseSegsOrThrow pat)

/-- A `mount` row's prefix: rejects any `.capture` segment, since mount prefixes are literal-only
(see module docstring). -/
private meta def prefixSegsFor (pat : TSyntax `str) : CommandElabM (List PathSeg) := do
  let segs ← parseSegsOrThrow pat
  if segs.any (fun | .capture .. => true | .lit _ _ => false) then
    throwErrorAt pat s!"mount prefix must not contain captures (got {pat.getString.quote}); captured mount prefixes are not yet supported"
  pure segs

/-- Lean source text for a `List String` literal. -/
private meta def stringsListSrc (strs : List String) : String :=
  "[" ++ String.intercalate ", " (strs.map String.quote) ++ "]"

/-- Resolves `sub` (a `mount` row's app identifier) to its generated `Patterns` structure,
accounting for the current namespace/opens the same way a plain identifier typed by the user
would resolve. Fails loudly if `sub` doesn't name a `route_table`-generated app, rather than
risking `getStructureFields` silently treating a non-structure as having no fields. -/
private meta def resolveSubPatterns (sub : Ident) : CommandElabM Name := do
  let patternsId := mkIdentFrom sub (sub.getId ++ `Patterns)
  let name ← resolveGlobalConstNoOverload patternsId
  unless isStructure (← getEnv) name do
    throwErrorAt sub s!"'{sub.getId}' is not a route_table-generated app (no structure '{name}')"
  pure name

/-- `some structName` if `field` of `structName` is itself a `route_table`-generated `Patterns`-
shaped structure (i.e. `field` came from a `mount` row when `structName`'s table was declared);
`none` if it's a leaf field (`List Routing.PathSeg`). Reads the field's type off its projection
function's declared type (`∀ (self : structName), FieldType`) rather than the field's *value*,
since this only needs to classify the shape, not evaluate anything. -/
private meta def mountedFieldStruct? (env : Environment) (structName field : Name) :
    CommandElabM (Option Name) := do
  let some info := getFieldInfo? env structName field
    | throwError "internal error: field '{field}' not found on '{structName}'"
  let some ci := env.find? info.projFn
    | throwError "internal error: projection '{info.projFn}' not found"
  let .forallE _ _ body _ := ci.type
    | throwError "internal error: projection '{info.projFn}' has unexpected type"
  let some head := body.getAppFn.constName?
    | throwError "internal error: field '{field}' has unexpected type shape"
  if head == `List then
    pure none
  else if isStructure env head then
    pure (some head)
  else
    throwError "internal error: field '{field}' has unrecognized type head '{head}'"

/-- How deeply `mount` rows may nest. The walk below needs some bound to be a total function, and
mount chains are short by construction: each level is a separately-declared feature module. -/
private meta def maxMountDepth : Nat := 64

/-- The field every generated `Patterns` and `Links` carries for the prefix its table is mounted
under, which is why a row may not take its name. -/
private meta def mountedAtField : Name := `mountedAt

/-- Recursively walks `structName` (a `Patterns`-shaped structure, reachable via `accessSrc`, Lean
source text for a value of that type, e.g. `"BlogRoutes.patterns"`), building the
`field := ..., ...` source for both the prefixed `Patterns` value and the corresponding `Links`
value. Recurses into fields that are themselves mounted sub-tables (`mountedFieldStruct?`), so a
mount nests to whatever depth the sub-table itself nests; `pre` is the same at every depth, since a
mount's prefix applies to everything under it. Links values are computed from the *Patterns* side
(`Routing.linkFor` applied to the prefixed segs), same as a leaf row does; there's no pre-built
link function to unwrap. -/
private meta def mountFieldsSrc (env : Environment) (fuel : Nat) (structName : Name) (accessSrc : String)
    (pre : List PathSeg) : CommandElabM (String × String) := do
  match fuel with
  | 0 => throwError "mounted route tables nest more than {maxMountDepth} levels deep at '{structName}'"
  | fuel + 1 =>
    let prefixSegsSrc := segsListSrc pre
    let mut patFields : Array String := #[]
    let mut linkFields : Array String := #[]
    for f in getStructureFields env structName do
      let childAccessSrc := s!"{accessSrc}.{f}"
      if f == mountedAtField then
        let mountedAtSrc :=
          s!"Routing.MountPoint.append (.mk {stringsListSrc (pre.map PathSeg.toString)}) {childAccessSrc}"
        patFields := patFields.push s!"{f} := {mountedAtSrc}"
        linkFields := linkFields.push s!"{f} := Routing.mountLink ({mountedAtSrc}).segs"
        continue
      match ← mountedFieldStruct? env structName f with
      | none =>
          patFields := patFields.push s!"{f} := Routing.mountSegs {prefixSegsSrc} {childAccessSrc}"
          linkFields := linkFields.push s!"{f} := Routing.linkFor (Routing.mountSegs {prefixSegsSrc} {childAccessSrc})"
      | some nestedStructName =>
          let (nestedPat, nestedLink) ←
            mountFieldsSrc env fuel nestedStructName childAccessSrc pre
          patFields := patFields.push (s!"{f} := " ++ "{ " ++ nestedPat ++ " }")
          linkFields := linkFields.push (s!"{f} := " ++ "{ " ++ nestedLink ++ " }")
    pure (String.intercalate ", " patFields.toList, String.intercalate ", " linkFields.toList)
termination_by fuel

/-- One row's generated field: its `Patterns`/`Links` field type and value, as Lean source text.
Computed once per row (`rowGenFor`), reused below by both `Patterns` (3/4) and `Links` (5/6). -/
private meta structure RowGen where
  name : Ident
  patternsFieldTypeSrc : String
  patternsValueSrc : String
  linksFieldTypeSrc : String
  linksValueSrc : String

private meta def rowGenFor (env : Environment) (name : Ident) : RowKind → CommandElabM RowGen
  | .leaf pat => do
      let segsSrc ← segsSrcFor pat
      pure
        { name
          patternsFieldTypeSrc := "List Routing.PathSeg"
          patternsValueSrc := segsSrc
          linksFieldTypeSrc := s!"Routing.LinkType {segsSrc}"
          linksValueSrc := s!"Routing.linkFor {segsSrc}" }
  | .mount prefixPat sub => do
      let pre ← prefixSegsFor prefixPat
      let subPatterns ← resolveSubPatterns sub
      let subApp := subPatterns.getPrefix
      let (patFieldsSrc, linkFieldsSrc) ←
        mountFieldsSrc env maxMountDepth subPatterns s!"{subApp}.patterns" pre
      pure
        { name
          patternsFieldTypeSrc := toString subPatterns
          patternsValueSrc := "{ " ++ patFieldsSrc ++ " }"
          linksFieldTypeSrc := toString (subApp ++ `Links)
          linksValueSrc := "{ " ++ linkFieldsSrc ++ " }" }

elab_rules : command
  | `(route_table $appId:ident [ $rows,* ]) => do
    let appName := appId.getId
    -- 1. Destructure each row into (name, row kind): a plain pattern (`RowKind.leaf`) or a
    -- mount of another app under a literal prefix (`RowKind.mount`).
    let entries ← rows.getElems.mapM fun row => do
      match row with
      | `(routeTableRow| $name:ident := $pat:str) => pure (name, RowKind.leaf pat)
      | `(routeTableRow| $name:ident := mount $prefixPat:str $sub:ident) =>
          pure (name, RowKind.mount prefixPat sub)
      | _ => throwUnsupportedSyntax

    -- 2. Reject a name declared twice; each name denotes exactly one pattern or mount,
    -- regardless of row kind.
    let mut seen : Std.HashMap Name Syntax := {}
    for (name, _) in entries do
      if name.getId == mountedAtField then
        throwErrorAt name
          s!"route name '{mountedAtField}' is reserved for the prefix the table is mounted under"
      if let some prior := seen[name.getId]? then
        throwErrorAt name s!"route name '{name.getId}' already declared at {prior}"
      seen := seen.insert name.getId name

    -- Compute each row's field type/value source once here (`rowGenFor`), reused below by both
    -- `Patterns` (3/4) and `Links` (5/6), rather than each recomputing it separately.
    let env ← getEnv
    let rowGens ← entries.mapM fun (name, kind) => rowGenFor env name kind

    -- 3/4. `structure App.Patterns where name : List Routing.PathSeg ...` and
    -- `def App.patterns : App.Patterns := { name := [PathSeg literal], ... }`.
    --
    -- Built as source text and reparsed (`elabCommandFromSource` above) rather than spliced via
    -- `$[...]*` antiquotations: `structure`'s field list (`structFields`, `Parser/Command.lean`)
    -- is a `manyIndent`, which depends on column tracking that synthetic `Syntax` doesn't carry,
    -- so the antiquotation form silently parses as a zero-field structure. (Same technique reused
    -- below for `App.Links`/`App.links`.)
    --
    -- A leaf row's field is typed by an already-parsed `List PathSeg` *literal* (`segsSrcFor`),
    -- not a pattern-string call for the elaborator to reduce, so a `Route` built from a field
    -- (`Route.get`/`.post`/etc., `Route.lean`) needs no further parsing. A mount row's field
    -- reuses the sub-app's own `Patterns` structure type (`rowGenFor`'s `.mount` case): a
    -- literal prefix never changes a `Patterns` field's type, only its value.
    let patternsTypeIdent := qualifyPlain appId appName `Patterns
    let patternsValIdent := qualifyPlain appId appName `patterns
    let patternFieldsSrc := String.intercalate "\n  " <|
      s!"{mountedAtField} : Routing.MountPoint" ::
        rowGens.toList.map fun g => s!"{g.name.getId} : {g.patternsFieldTypeSrc}"
    elabCommandFromSource appId
      s!"structure {patternsTypeIdent.getId} where\n  {patternFieldsSrc}"

    let expose ← exposeSrc
    let patternValFieldsSrc := String.intercalate ", " <|
      s!"{mountedAtField} := .mk []" ::
        rowGens.toList.map fun g => s!"{g.name.getId} := {g.patternsValueSrc}"
    elabCommandFromSource appId <|
      expose ++ "def " ++ toString patternsValIdent.getId ++ " : " ++
        toString patternsTypeIdent.getId ++ " := { " ++ patternValFieldsSrc ++ " }"

    -- So a `Router` mount (`Router.lean`) can name a table by its `patterns` value.
    elabCommandFromSource appId <|
      s!"instance {appName ++ `instCoeMountPoint} : Coe " ++ toString patternsTypeIdent.getId ++
        " Routing.MountPoint := ⟨(·.mountedAt)⟩"

    -- 5/6. `structure App.Links where name : LinkType [PathSeg literal] ...` and
    -- `def App.links : App.Links := { name := linkFor [PathSeg literal], ... }`.
    --
    -- Same source-text-and-reparse technique as 3/4 above (see that comment for why). A leaf
    -- row's field is typed by `LinkType [PathSeg literal]`, not `LinkType App.Patterns.name`: a
    -- zero-capture field has no argument application to force reduction through a *reference* to
    -- the `Patterns` field, so it must splice the literal (`rowGens`, computed once above)
    -- directly. A mount row's field reuses the sub-app's own `Links` structure type, for the same
    -- reason its `Patterns` field does.
    let linksTypeIdent := qualifyPlain appId appName `Links
    let linksValIdent := qualifyPlain appId appName `links
    let structFieldsSrc := String.intercalate "\n  " <|
      s!"{mountedAtField} : String" ::
        rowGens.toList.map fun g => s!"{g.name.getId} : {g.linksFieldTypeSrc}"
    elabCommandFromSource appId
      s!"structure {linksTypeIdent.getId} where\n  {structFieldsSrc}"

    let valFieldsSrc := String.intercalate ", " <|
      s!"{mountedAtField} := Routing.mountLink []" ::
        rowGens.toList.map fun g => s!"{g.name.getId} := {g.linksValueSrc}"
    elabCommandFromSource appId <|
      expose ++ "def " ++ toString linksValIdent.getId ++ " : " ++
        toString linksTypeIdent.getId ++ " := { " ++ valFieldsSrc ++ " }"

end Routing
