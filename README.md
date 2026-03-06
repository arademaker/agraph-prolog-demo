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

?- grandparent(tom, ann).   % true
?- sibling(bob, liz).       % true
```

## Approaches Explored

### [`Demo/Basic.lean`](Demo/Basic.lean) — Hardcoded Facts

**Approach 1: Propositions as types.** Each Prolog fact becomes a constructor of an inductive `Prop`. Queries are *proofs* verified at compile-time. The type checker is the search engine.

```lean
inductive Parent : Person -> Person -> Prop where
  | tom_bob : Parent tom bob
  ...
example : Grandparent tom ann :=
  Grandparent.intro bob Parent.tom_bob Parent.bob_ann
```

**Approach 2: Decidable functions.** Relations become `Bool`-returning functions. Queries compute results at runtime via `List.filter` / `List.flatMap` — the closest to Prolog's runtime behavior.

```lean
def isParent : Person -> Person -> Bool
  | tom, bob => true  ...
#eval grandchildren tom  -- [ann, pat]
```

**Approach 3: Type classes as Prolog.** Lean's type class resolution *is* essentially a Prolog engine ([Aarsen et al., 2020](https://arxiv.org/abs/2001.04301v1)): `class ~ predicate`, `instance ~ clause`, `resolution ~ SLD with backtracking`. The elaborator resolves queries automatically.

```lean
class IsParent (x : Person) (y : outParam Person)
instance : IsParent tom bob where
#check (inferInstance : IsGrandparent tom ann)  -- ok!
```

**Limitation:** `outParam` makes relations functional (one result per input). Multi-valued relations like `sibling` require explicit facts or a different encoding.

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

**Queries:**
- Prolog `?- grandparent(tom, ann).` →
  - Props: `example : Grandparent tom ann := ...` (a proof term)
  - Functions: `#eval grandchildren tom` (computes `[ann, pat]`)
  - Type classes: `inferInstance : IsGrandparent tom ann` (resolved by elaborator)

**Loading external facts:**
- Prolog `consult('file.pl').` →
  - `IO.FS.readFile` (runtime), `#load_family` (compile-time lists), `#consult_prop` (compile-time inductive Prop), or `#consult` (compile-time type classes)

**Negation and backtracking:**
- Prolog negation `\+` → `¬` with proof (Props), `!= / filter` (functions), not natively supported (type classes)
- Prolog backtracking → proof search (Props), `List` operations (functions), limited by `outParam` (type classes)

## Building and Running

```sh
lake build        # builds everything, #guard_msgs verifies all queries
lake exec demo    # runs the runtime IO demo
```

## Notes on Metaprogramming

Approaches C and D use Lean's `elab` to generate code at compile-time. Approach D uses **syntax quotations** (`` `(command| ...) ``), which work well for type class declarations and instances.

Approach C, however, needs to generate an **indexed inductive type** where each constructor specifies a different return type (e.g., `| tom_bob : Parent .tom .bob`). Lean's quotation syntax does not currently support splicing constructor arrays into indexed inductives — the `rawIdent` in the constructor parser and the type signature `T : A -> A -> Prop` interact poorly with antiquotation. As a workaround, Approach C builds a source string and parses it with `Parser.runParserCategory`. This is a known ergonomic gap in Lean's metaprogramming API for indexed inductive families.
