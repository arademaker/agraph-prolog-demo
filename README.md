# Lean for Prolog Programmers

A demo project showing how to implement classic Prolog patterns in Lean 4, using the standard family relations example. The goal is to show users familiar with Prolog — such as those coming from [AllegroGraph's Prolog tutorial](https://franz.com/agraph/support/documentation/prolog-tutorial.html) — how a similar approach can be implemented in Lean.

## The Prolog Example

```prolog
parent(tom, bob).
parent(tom, liz).
parent(bob, ann).
parent(bob, pat).

grandparent(X, Z) :- parent(X, Y), parent(Y, Z).
sibling(X, Y) :- parent(Z, X), parent(Z, Y), X \= Y.
ancestor(X, Y) :- parent(X, Y).
ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).

?- grandparent(tom, ann).   % true
?- sibling(bob, liz).       % true
?- ancestor(tom, pat).      % true (tom -> bob -> pat)
```

## Approaches Explored

### [`Demo/Basic.lean`](Demo/Basic.lean) — Hardcoded Facts

**Approach 1: Propositions as types.** Each Prolog fact becomes a constructor of an inductive `Prop`. Queries are *proofs* verified at compile-time. Includes `Parent`, `Grandparent`, `Sibling`, and `Ancestor` (recursive — transitive closure of `Parent`).

```lean
inductive Ancestor : Person → Person → Prop where
  | base : Parent x y → Ancestor x y
  | step : Parent x mid → Ancestor mid y → Ancestor x y

-- The proof *is* the derivation tree: tom → bob → ann
example : Ancestor tom ann :=
  Ancestor.step Parent.tom_bob (Ancestor.base Parent.bob_ann)
```

**Bridging Prop and Bool: `Decidable`.** Prolog conflates truth and computation. Lean separates them — but `Decidable` reconnects them. With a `Decidable` instance, the `decide` tactic becomes automated proof search, Lean's closest analog to Prolog's resolution engine.

```lean
instance : Decidable (Parent x y) := ...
example : Parent tom bob := by decide       -- automated!
example : ¬ Parent liz ann := by decide     -- automated!
```

**Approach 2: Decidable functions.** Relations become `Bool`-returning functions. Queries compute results at runtime via `List.filter` / `List.flatMap` — the closest to Prolog's runtime behavior. Includes `ancestors` (transitive closure via worklist algorithm).

```lean
#eval ancestors tom  -- [bob, liz, ann, pat]
```

**Approach 3: Type classes as Prolog.** Lean's type class resolution *is* essentially a Prolog engine ([Aarsen et al., 2020](https://arxiv.org/abs/2001.04301v1)): `class ~ predicate`, `instance ~ clause`, `resolution ~ SLD with backtracking`. The elaborator resolves queries automatically.

```lean
class IsParent (x : Person) (y : outParam Person)
instance : IsParent tom bob := {}
#check (inferInstance : IsGrandparent tom ann)  -- ok!
```

**Limitations:** `outParam` makes relations functional (one result per input). Multi-valued relations like `sibling` require explicit facts. Recursive predicates like `ancestor` cannot be encoded — the resolver would loop. This illustrates a key point: type classes are a *fragment* of Prolog.

### [`Demo/FromFile.lean`](Demo/FromFile.lean) — Facts from a File

**Approach A: Runtime (IO).** Read [`data/family.txt`](data/family.txt), parse it into a `FamilyDB` structure, query with functions. Simple, no metaprogramming.

**Approach B: Compile-time lists.** The `#load_family` elaboration command reads the file during compilation and generates `def loadedPersons` / `def loadedParents` — pure Lean constants, no IO needed to use them.

**Approach C: Compile-time inductive Prop.** The `#consult_prop` command generates an indexed inductive proposition `Parent : Person → Person → Prop` (in the `FromFile` namespace) from the file — like Approach 1 in `Basic.lean`, but with constructors generated from external data. This enables writing *proofs* about the loaded relations (e.g., `example : ¬ Parent .liz .ann`).

**Approach D: Compile-time type classes.** The `#consult` command (named after Prolog's `consult/1`) reads the file and generates a `class IsParent (x y : Person)` (in the `FromFile` namespace) with one `instance` per `parent` line. It reuses the same `Person` type from `Basic.lean`. After `#consult "data/family.txt"`, the type class resolver works exactly like Prolog — `inferInstance : IsParent .tom .bob` resolves automatically.

## Prolog to Lean Mapping

**Atoms and facts:**
- Prolog atom `tom` → `Person.tom` (inductive constructor) or `"tom"` (string)
- Prolog fact `parent(tom, bob).` → `Parent.tom_bob` (Prop constructor), `isParent tom bob = true` (function), or `instance : IsParent tom bob` (type class)

**Rules:**
- Prolog `grandparent(X, Z) :- parent(X, Y), parent(Y, Z).` →
  - Props: `Grandparent.intro` constructor requiring two `Parent` evidences
  - Functions: `grandchildren` via `List.flatMap`
  - Type classes: `instance [IsParent x y] [IsParent y z] : IsGrandparent x z`

**Recursive rules:**
- Prolog `ancestor(X, Y) :- parent(X, Y). ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).` →
  - Props: `Ancestor` inductive with `base` and `step` constructors
  - Functions: `ancestors` via worklist/BFS (termination must be guaranteed)
  - Type classes: **not possible** — recursive instances cause the resolver to loop

**Queries:**
- Prolog `?- grandparent(tom, ann).` →
  - Props: `example : Grandparent tom ann := ...` (a proof term)
  - Functions: `#eval grandchildren tom` (computes `[ann, pat]`)
  - Type classes: `inferInstance : IsGrandparent tom ann` (resolved by elaborator)
  - Decidable: `example : Grandparent tom ann := by decide` (automated search)

**Loading external facts:**
- Prolog `consult('file.pl').` →
  - `IO.FS.readFile` (runtime), `#load_family` (compile-time lists), `#consult_prop` (compile-time inductive Prop), or `#consult` (compile-time type classes)

**Negation:**
- Prolog `\+` is *negation as failure* (closed-world assumption): if no clause proves it, it's false
- Lean `¬` is *constructive*: you must prove impossibility by exhausting all cases (`cases h`)
- Lean `Bool` functions naturally implement closed-world via `| _, _ => false`
- `Decidable` bridges both: `example : ¬ Parent liz ann := by decide`

**Backtracking:**
- Prolog backtracking → proof search (Props), `List` operations (functions), limited by `outParam` (type classes)

## Building and Running

```sh
lake build        # builds everything, #guard_msgs verifies all queries
lake exec demo    # runs the runtime IO demo
```

## Notes on Metaprogramming

Approaches C and D use Lean's `elab` to generate code at compile-time. Approach D uses **syntax quotations** (`` `(command| ...) ``), which work well for type class declarations and instances.

Approach C, however, needs to generate an **indexed inductive type** where each constructor specifies a different return type (e.g., `| tom_bob : Parent .tom .bob`). Lean's quotation syntax does not currently support splicing constructor arrays into indexed inductives — the `rawIdent` in the constructor parser and the type signature `T : A -> A -> Prop` interact poorly with antiquotation. As a workaround, Approach C builds a source string and parses it with `Parser.runParserCategory`. This is a known ergonomic gap in Lean's metaprogramming API for indexed inductive families.
