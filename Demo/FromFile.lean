import Lean
-- ============================================================
-- Lean for Prolog Programmers: Loading Facts from a File
-- ============================================================
-- In Prolog, you can load facts from a file with consult/1.
-- In Lean, we have several options:
--
--   A) Runtime (IO): read the file, parse it, and use functions.
--      Simple, no metaprogramming. Equivalent to a normal program.
--
--   B) Compile-time (elaboration): read the file during compilation
--      and generate Lean definitions. Uses metaprogramming.
--      The data becomes code verified by the type checker.
--
--   C) Compile-time (elaboration): generate an inductive type and
--      type class instances from the file. The closest equivalent
--      to Prolog's consult/1.

-- ============================================================
-- Approach A: Runtime — read data and compute with IO
-- ============================================================

structure FamilyDB where
  persons : List String
  parents : List (String × String)
  deriving Repr, Inhabited

def parseLine (line : String) : Option (String × List String) :=
  let parts := line.trimAscii.toString.splitOn " " |>.filter (· != "")
  match parts with
  | [] => none
  | keyword :: args => some (keyword, args)

def parseFamily (contents : String) : FamilyDB :=
  let lines := contents.splitOn "\n"
  let entries := lines.filterMap parseLine
  let persons := entries.filterMap fun (kw, args) =>
    if kw == "person" then args.head? else none
  let parents := entries.filterMap fun (kw, args) =>
    if kw == "parent" then
      match args with
      | [p, c] => some (p, c)
      | _ => none
    else none
  { persons, parents }

def FamilyDB.childrenOf (db : FamilyDB) (p : String) : List String :=
  db.parents.filterMap fun (par, child) =>
    if par == p then some child else none

def FamilyDB.grandchildrenOf (db : FamilyDB) (p : String) : List String :=
  (db.childrenOf p).flatMap db.childrenOf

def FamilyDB.siblingsOf (db : FamilyDB) (p : String) : List String :=
  let parentsOfP := db.parents.filterMap fun (par, child) =>
    if child == p then some par else none
  let sibs := parentsOfP.flatMap db.childrenOf
  sibs.filter (· != p)

-- Main program: reads the file and runs queries
def runtimeDemo : IO Unit := do
  let contents ← IO.FS.readFile "data/family.txt"
  let db := parseFamily contents
  IO.println s!"Persons: {db.persons}"
  IO.println s!"Children of tom: {db.childrenOf "tom"}"
  IO.println s!"Grandchildren of tom: {db.grandchildrenOf "tom"}"
  IO.println s!"Siblings of bob: {db.siblingsOf "bob"}"
  IO.println s!"Siblings of ann: {db.siblingsOf "ann"}"

-- ============================================================
-- Approach B: Compile-time — elaboration that reads a file
-- ============================================================
-- We use Lean's metaprogramming system to read the file during
-- compilation and generate real Lean definitions.
-- This is the equivalent of Prolog's `consult/1`!

open Lean Syntax Elab Command in
elab "#load_family " path:str : command => do
  let contents ← IO.FS.readFile path.getString
  let db := parseFamily contents
  let personStx : Array (TSyntax `term) ← db.persons.toArray.mapM fun name =>
    `($(Lean.quote name))
  let parentStx : Array (TSyntax `term) ← db.parents.toArray.mapM fun (p, c) =>
    `(($(Lean.quote p), $(Lean.quote c)))
  let pSep : TSepArray `term "," := TSepArray.ofElems personStx
  let parSep : TSepArray `term "," := TSepArray.ofElems parentStx
  let personsId := mkIdent `loadedPersons
  let parentsId := mkIdent `loadedParents
  let cmd1 ← `(command| def $personsId : List String := [$pSep,*])
  Lean.Elab.Command.elabCommand cmd1
  let cmd2 ← `(command| def $parentsId : List (String × String) := [$parSep,*])
  Lean.Elab.Command.elabCommand cmd2

-- Load the data from file at compile-time!
#load_family "data/family.txt"

-- Now we have pure Lean constants, no IO needed:

/-- info: ["tom", "bob", "liz", "ann", "pat"] -/
#guard_msgs in
#eval loadedPersons

/-- info: [("tom", "bob"), ("tom", "liz"), ("bob", "ann"), ("bob", "pat")] -/
#guard_msgs in
#eval loadedParents

-- We can compute with them normally:
def loadedChildren (p : String) : List String :=
  loadedParents.filterMap fun (par, child) =>
    if par == p then some child else none

/-- info: ["bob", "liz"] -/
#guard_msgs in
#eval loadedChildren "tom"

/-- info: ["ann", "pat"] -/
#guard_msgs in
#eval loadedChildren "bob"


-- ============================================================
-- Approach C: Compile-time — generate type class instances
-- ============================================================
-- Here we go further: instead of generating lists, we generate
-- an inductive type for persons and type class instances for the
-- facts. This is the closest to Prolog's `consult/1`: the data
-- from the file becomes predicates resolved by the elaborator
-- automatically.
--
-- The file generates code equivalent to:
--   inductive FPerson where | tom | bob | liz | ann | pat
--   class FParent (x y : FPerson)
--   instance : FParent .tom .bob
--   instance : FParent .tom .liz
--   ...
--
-- See also Approach D below, which generates an inductive Prop
-- instead of a type class.

open Lean Syntax Elab Command in
elab "#consult " path:str : command => do
  let contents ← IO.FS.readFile path.getString
  let db := parseFamily contents
  -- 1. Generate: inductive FPerson where | tom | bob | ...
  let ctors : Array (TSyntax ``Parser.Command.ctor) ← db.persons.toArray.mapM fun name => do
    let id := mkIdent (Name.mkSimple name)
    `(Parser.Command.ctor| | $id:ident)
  let fpersonId := mkIdent `FPerson
  let inductiveCmd ← `(command| inductive $fpersonId where $ctors*)
  Lean.Elab.Command.elabCommand inductiveCmd
  -- 2. Generate: class FParent (x y : FPerson) where
  let fparentId := mkIdent `FParent
  let classCmd ← `(command|
    class $fparentId (x y : $fpersonId) where)
  Lean.Elab.Command.elabCommand classCmd
  -- 3. Generate one instance per parent pair
  for (p, c) in db.parents do
    let pid := mkIdent (Name.mkStr `FPerson p)
    let cid := mkIdent (Name.mkStr `FPerson c)
    let instCmd ← `(command| instance : $fparentId $pid $cid where)
    Lean.Elab.Command.elabCommand instCmd

-- Load everything from the file!
#consult "data/family.txt"

-- Now we have the type and instances generated automatically.
-- Lean's type class resolver works like Prolog:

/-- info: inferInstance : FParent FPerson.tom FPerson.bob -/
#guard_msgs in
#check (inferInstance : FParent .tom .bob)

/-- info: inferInstance : FParent FPerson.bob FPerson.ann -/
#guard_msgs in
#check (inferInstance : FParent .bob .ann)

-- Query that fails — equivalent to "false" in Prolog:
/--
error: failed to synthesize instance of type class
  FParent FPerson.liz FPerson.ann

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#check (inferInstance : FParent .liz .ann)


-- ============================================================
-- Approach D: Compile-time — generate inductive Prop
-- ============================================================
-- Like Approach 1 in Basic.lean, but the inductive type is
-- generated from the file. Each parent pair becomes a named
-- constructor of an inductive Prop:
--
--   inductive FParentProp : FPerson → FPerson → Prop where
--     | tom_bob : FParentProp .tom .bob
--     | tom_liz : FParentProp .tom .liz
--     | bob_ann : FParentProp .bob .ann
--     | bob_pat : FParentProp .bob .pat
--
-- This gives us the full power of Approach 1: we can write
-- proofs about the relations, not just check them.

open Lean Elab Command in
elab "#consult_prop " path:str : command => do
  let contents ← IO.FS.readFile path.getString
  let db := parseFamily contents
  -- Reuse FPerson from #consult (already defined above).
  -- We build the source string and parse it, because quotation
  -- syntax doesn't support indexed inductive types well (the
  -- constructors need explicit return types like
  -- `| tom_bob : FParentProp .tom .bob`).
  let ctorLines := db.parents.map fun (p, c) =>
    s!"  | {p}_{c} : FParentProp FPerson.{p} FPerson.{c}"
  let src := "inductive FParentProp : FPerson → FPerson → Prop where\n"
    ++ "\n".intercalate ctorLines
  let env ← getEnv
  match Parser.runParserCategory env `command src with
  | .error msg => throwError msg
  | .ok stx => elabCommand stx

#consult_prop "data/family.txt"

-- Now we can write proofs, just like Approach 1 in Basic.lean:
example : FParentProp .tom .bob := FParentProp.tom_bob
example : FParentProp .bob .ann := FParentProp.bob_ann

-- And prove negation — liz is not a parent of ann:
example : ¬ FParentProp .liz .ann := by
  intro h; cases h
