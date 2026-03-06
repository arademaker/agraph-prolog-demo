import Lean
import Demo.Basic

/- ============================================================
   Lean for Prolog Programmers: Loading Facts from a File
   ============================================================
   In Prolog, you can load facts from a file with consult/1.
   In Lean, we have several options:

     A) Runtime (IO): read the file, parse it, and use functions.
        Simple, no metaprogramming. Equivalent to a normal program.

     B) Compile-time (elaboration): read the file during compilation
        and generate Lean definitions. Uses metaprogramming.
        The data becomes code verified by the type checker.

     C) Compile-time: generate an inductive Prop from the file
        (like Approach 1 in Basic.lean).

     D) Compile-time: generate type class instances from the file
        (like Approach 3 in Basic.lean).

   We use a namespace `FromFile` so that the generated names
   (Parent, IsParent) match those in Basic.lean without conflict. -/

namespace FromFile

/- ============================================================
   Approach A: Runtime — read data and compute with IO
   ============================================================ -/

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

/- Transitive closure: find all ancestors (descendants reachable
   from p via the parent relation). Uses a worklist algorithm
   to avoid infinite loops on cyclic data. -/
def FamilyDB.ancestorsOf (db : FamilyDB) (p : String) : List String :=
  let rec go (fuel : Nat) (frontier visited : List String) : List String :=
    match fuel, frontier with
    | 0, _          => visited
    | _, []         => visited
    | n + 1, x :: rest =>
      let newChildren := (db.childrenOf x).filter (· ∉ visited)
      go n (rest ++ newChildren) (visited ++ newChildren)
  let init := db.childrenOf p
  go db.persons.length init init

-- Main program: reads the file and runs queries
def runtimeDemo : IO Unit := do
  let contents ← IO.FS.readFile "data/family.txt"
  let db := parseFamily contents
  IO.println s!"Persons: {db.persons}"
  IO.println s!"Children of tom: {db.childrenOf "tom"}"
  IO.println s!"Grandchildren of tom: {db.grandchildrenOf "tom"}"
  IO.println s!"Siblings of bob: {db.siblingsOf "bob"}"
  IO.println s!"Siblings of ann: {db.siblingsOf "ann"}"
  IO.println s!"Ancestors of tom: {db.ancestorsOf "tom"}"


/- ============================================================
   Approach B: Compile-time — elaboration that reads a file
   ============================================================
   We use Lean's metaprogramming system to read the file during
   compilation and generate real Lean definitions.
   This is the equivalent of Prolog's `consult/1`! -/

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


/- ============================================================
   Approach C: Compile-time — generate inductive Prop
   ============================================================
   Like Approach 1 in Basic.lean, but the inductive type is
   generated from the file. Each parent pair becomes a named
   constructor of an inductive Prop:

     inductive Parent : Person → Person → Prop where
       | tom_bob : Parent .tom .bob
       | tom_liz : Parent .tom .liz
       | bob_ann : Parent .bob .ann
       | bob_pat : Parent .bob .pat

   This gives us the full power of Approach 1: we can write
   proofs about the relations, not just check them. -/

open Lean Elab Command in
elab "#consult_prop " path:str : command => do
  let contents ← IO.FS.readFile path.getString
  let db := parseFamily contents
  /- We build the source string and parse it, because quotation
     syntax doesn't support indexed inductive types well (the
     constructors need explicit return types like
     `| tom_bob : Parent .tom .bob`). -/
  let ctorLines := db.parents.map fun (p, c) =>
    s!"  | {p}_{c} : FromFile.Parent Person.{p} Person.{c}"
  let src := "inductive FromFile.Parent : Person → Person → Prop where\n"
    ++ "\n".intercalate ctorLines
  let env ← getEnv
  match Parser.runParserCategory env `command src with
  | .error msg => throwError msg
  | .ok stx => elabCommand stx

end FromFile

#consult_prop "data/family.txt"

namespace FromFile

-- Now we can write proofs, just like Approach 1 in Basic.lean:
example : Parent .tom .bob := Parent.tom_bob
example : Parent .bob .ann := Parent.bob_ann

-- And prove negation — liz is not a parent of ann:
example : ¬ Parent .liz .ann := by
  intro h; cases h


/- ============================================================
   Approach D: Compile-time — generate type class instances
   ============================================================
   Like Approach 3 in Basic.lean, but the instances are generated
   from the file. We reuse Person and generate a class IsParent
   with one instance per parent line.

   The file generates code equivalent to:
     class IsParent (x y : Person)
     instance : IsParent .tom .bob
     instance : IsParent .tom .liz
     ... -/

open Person in
open Lean Syntax Elab Command in
elab "#consult " path:str : command => do
  let contents ← IO.FS.readFile path.getString
  let db := FromFile.parseFamily contents
  -- Generate: class FromFile.IsParent (x y : Person)
  let classId := mkIdent `FromFile.IsParent
  let personId := mkIdent `Person
  let classCmd ← `(command|
    class $classId (x y : $personId))
  Lean.Elab.Command.elabCommand classCmd
  -- Generate one instance per parent pair
  for (p, c) in db.parents do
    let pid := mkIdent (Name.mkStr `Person p)
    let cid := mkIdent (Name.mkStr `Person c)
    let instCmd ← `(command| instance : $classId $pid $cid := {})
    Lean.Elab.Command.elabCommand instCmd

end FromFile

#consult "data/family.txt"

namespace FromFile

/- Now we have instances generated automatically.
   Lean's type class resolver works like Prolog: -/

/-- info: inferInstance : IsParent Person.tom Person.bob -/
#guard_msgs in
#check (inferInstance : IsParent .tom .bob)

/-- info: inferInstance : IsParent Person.bob Person.ann -/
#guard_msgs in
#check (inferInstance : IsParent .bob .ann)

-- Query that fails — equivalent to "false" in Prolog:
/--
error: failed to synthesize instance of type class
  IsParent Person.liz Person.ann

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#check (inferInstance : IsParent .liz .ann)

end FromFile
