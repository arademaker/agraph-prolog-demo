/- ============================================================
   Lean for Prolog Programmers: Family Relations
   ============================================================ -/

/- In Prolog, you define "people" as atoms. In Lean, we use
   an inductive type (like an enum). -/
inductive Person where
  | tom | bob | liz | ann | pat
  deriving Repr, DecidableEq

open Person

/- ============================================================
   Approach 1: Propositions as types (the "Lean way")
   ============================================================
   In Prolog: parent(tom, bob).
   In Lean: Parent is an inductive proposition. Each constructor
   is equivalent to a Prolog *fact*. -/

inductive Parent : Person → Person → Prop where
  | tom_bob : Parent tom bob
  | tom_liz : Parent tom liz
  | bob_ann : Parent bob ann
  | bob_pat : Parent bob pat

/- In Prolog: grandparent(X, Z) :- parent(X, Y), parent(Y, Z).
   In Lean: a proposition that *requires* evidence from two Parents. -/

inductive Grandparent : Person → Person → Prop where
  | intro (mid : Person) :
    Parent x mid → Parent mid z → Grandparent x z

-- In Prolog: sibling(X, Y) :- parent(Z, X), parent(Z, Y), X \= Y.

inductive Sibling : Person → Person → Prop where
  | intro (par : Person) :
    Parent par x → Parent par y → x ≠ y → Sibling x y

/- In Prolog: ancestor(X, Y) :- parent(X, Y).
              ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
   This is *recursive* — the key feature of Prolog for graph traversal.
   In Lean, we model it as an inductive type with two constructors:
   a base case and a step case. -/

inductive Ancestor : Person → Person → Prop where
  | base : Parent x y → Ancestor x y
  | step : Parent x mid → Ancestor mid y → Ancestor x y

/- ---- Proofs as explanations of derivations ----
   Now we *prove* the queries. The compiler verifies! -/
-- ?- grandparent(tom, ann).
example : Grandparent tom ann :=
  Grandparent.intro bob Parent.tom_bob Parent.bob_ann

-- ?- sibling(bob, liz).
example : Sibling bob liz :=
  Sibling.intro tom Parent.tom_bob Parent.tom_liz (by decide)

-- ?- ancestor(tom, ann).
-- The proof *is* the derivation tree: tom → bob → ann
example : Ancestor tom ann :=
  Ancestor.step Parent.tom_bob (Ancestor.base Parent.bob_ann)

-- ?- ancestor(tom, pat). — a different path through the tree
example : Ancestor tom pat :=
  Ancestor.step Parent.tom_bob (Ancestor.base Parent.bob_pat)

-- Direct parent is also an ancestor (base case):
example : Ancestor tom bob :=
  Ancestor.base Parent.tom_bob

/- Negation: Prolog's `not` is "negation as failure" — under the
   closed-world assumption, if no clause proves it, it's false.
   Lean's `¬` is constructive: you must *prove* impossibility by
   exhausting all cases. The proof below shows there is no path
   from liz to ann — no Parent constructor starts with liz. -/
-- Helper: liz has no children in our family.
theorem not_parent_liz : ∀ x, ¬ Parent liz x := by
  intro x h; cases h

example : ¬ Ancestor liz ann := by
  intro h; cases h with
  | base h => exact not_parent_liz _ h
  | step h _ => exact not_parent_liz _ h

-- Helper: ann has no children in our family.
theorem not_parent_ann : ∀ x, ¬ Parent ann x := by
  intro x h; cases h

-- No path from ann back to tom (the graph is acyclic):
example : ¬ Ancestor ann tom := by
  intro h; cases h with
  | base h => exact not_parent_ann _ h
  | step h _ => exact not_parent_ann _ h

/- In Prolog, a derivation is a trace of the rules used.
   In Lean, a proof *is* that trace — and the compiler checks it. -/

/- "Sibling is symmetric" — mirrors the Prolog rule:
     sibling(X, Y) :- parent(Z, X), parent(Z, Y), X \= Y.
   If we have evidence for Sibling x y, we can build
   evidence for Sibling y x by swapping the two Parent proofs. -/
theorem sibling_symm : Sibling x y → Sibling y x := by
  intro ⟨par, hx, hy, hne⟩
  exact Sibling.intro par hy hx (Ne.symm hne)

/- "ann and pat are siblings, and they are the *only* sibling
   pair among bob's children." The proof enumerates all ways
   bob can be parent of two distinct children. -/
example : ∀ x y, Parent bob x → Parent bob y → x ≠ y
  → (x = ann ∧ y = pat) ∨ (x = pat ∧ y = ann) := by
  intro x y hx hy hne
  cases hx <;> cases hy <;> simp_all


/- ============================================================
   Approach 2: Decidable functions (computational queries)
   ============================================================
   If you want something closer to Prolog at runtime
   (computing results, listing solutions), use functions. -/

def isParent : Person → Person → Bool
  | tom, bob => true
  | tom, liz => true
  | bob, ann => true
  | bob, pat => true
  | _,   _   => false

def children (p : Person) : List Person :=
  [tom, bob, liz, ann, pat].filter (isParent p ·)

def grandchildren (p : Person) : List Person :=
  (children p).flatMap children

-- Equivalent to ?- grandparent(tom, X).
#eval grandchildren tom

-- Equivalent to ?- parent(bob, X).
#eval children bob

-- Computational siblings
def siblings (p : Person) : List Person :=
  let parents := [tom, bob, liz, ann, pat].filter (isParent · p)
  let sibs := parents.flatMap children
  sibs.filter (· != p)

#eval siblings bob
#eval siblings ann

/- Transitive closure: ancestor(X, Y).
   In Prolog, recursion "just works" — the engine backtracks.
   In Lean, we must convince the termination checker that
   the recursion ends. For a finite set of persons, we use
   a visited-set to guarantee progress at each step. -/
private def allPersons : List Person := [tom, bob, liz, ann, pat]

def ancestors (p : Person) : List Person :=
  let rec go (fuel : Nat) (frontier visited : List Person) : List Person :=
    match fuel, frontier with
    | 0, _          => visited
    | _, []         => visited
    | n + 1, x :: rest =>
      let newChildren := children x |>.filter (· ∉ visited)
      go n (rest ++ newChildren) (visited ++ newChildren)
  go allPersons.length (children p) (children p)

-- Equivalent to ?- ancestor(tom, X). — finds bob, liz, ann, pat
/-- info: [Person.bob, Person.liz, Person.ann, Person.pat] -/
#guard_msgs in
#eval ancestors tom

-- Equivalent to ?- ancestor(bob, X).
/-- info: [Person.ann, Person.pat] -/
#guard_msgs in
#eval ancestors bob

-- liz has no descendants:
/-- info: [] -/
#guard_msgs in
#eval ancestors liz


/- ============================================================
   Bridging Propositions and Computation: Decidable
   ============================================================
   Prolog conflates truth and computation: a query is both a
   logical statement and a program that searches for a proof.
   Lean separates these: Approach 1 (Prop) is about truth,
   Approach 2 (Bool) is about computation. But `Decidable`
   reconnects them — it says "this Prop can be decided by
   an algorithm."

   With a Decidable instance, the `decide` tactic becomes
   an automated proof search — Lean's closest analog to
   Prolog's resolution engine. -/

instance : Decidable (Parent x y) :=
  match x, y with
  | tom, bob => isTrue Parent.tom_bob
  | tom, liz => isTrue Parent.tom_liz
  | bob, ann => isTrue Parent.bob_ann
  | bob, pat => isTrue Parent.bob_pat
  | tom, tom => isFalse (by intro h; cases h)
  | tom, ann => isFalse (by intro h; cases h)
  | tom, pat => isFalse (by intro h; cases h)
  | bob, tom => isFalse (by intro h; cases h)
  | bob, bob => isFalse (by intro h; cases h)
  | bob, liz => isFalse (by intro h; cases h)
  | liz, _ => isFalse (by intro h; cases h)
  | ann, _ => isFalse (by intro h; cases h)
  | pat, _ => isFalse (by intro h; cases h)

-- Now `decide` works as automated proof search:
example : Parent tom bob := by decide
example : ¬ Parent liz ann := by decide

-- Even compound queries:
example : Parent tom bob ∧ Parent bob ann := by decide
example : Parent tom bob ∨ Parent tom ann := by decide


/- ============================================================
   Approach 3: Type Classes as Prolog
   ============================================================
   Lean's type class mechanism *is* essentially a Prolog engine (cf.
   Aarsen et al., "Tabled Typeclass Resolution",
   https://arxiv.org/abs/2001.04301v1):

     class    ≈  Prolog predicate
     instance ≈  clause (fact or rule)
     type class resolution ≈  SLD resolution with backtracking

   The advantage: the *elaborator* performs the search automatically.
   You declare facts and rules, and Lean resolves the queries on its
   own — just like Prolog.

   HOWEVER: unlike pure Prolog, Lean's type class resolver requires a
   deterministic *synthesis order*. Free intermediate variables (like Y
   in grandparent) must be marked as `outParam` so the resolver knows
   where to start the search. -/

/- Facts: each instance is a parent(X, Y) fact.
   outParam marks y as "output" — given x, the resolver searches for y. -/
class IsParent (x : Person) (y : outParam Person)

instance : IsParent tom bob := {}
instance : IsParent tom liz := {}
instance : IsParent bob ann := {}
instance : IsParent bob pat := {}

/- Rule: grandparent(X, Z) :- parent(X, Y), parent(Y, Z).
   The resolver: given x, finds y via IsParent x y,
   then finds z via IsParent y z. -/
class IsGrandparent (x : Person) (z : outParam Person)

instance [IsParent x y] [IsParent y z] : IsGrandparent x z := {}

/- Queries: the elaborator resolves automatically!
   ?- grandparent(tom, ann).
   Lean finds: IsParent tom bob, IsParent bob ann → ok! -/

/-- info: inferInstance : IsGrandparent tom ann -/
#guard_msgs in
#check (inferInstance : IsGrandparent tom ann)

/- ?- grandparent(tom, pat).
   In Prolog, this would work via backtracking. But the type class
   resolver with outParam returns only the *first* match at each step:
   IsParent tom ? → bob, IsParent bob ? → ann.
   It never tries bob → pat. outParam makes the relation functional
   — only finds the first grandchild: -/
/--
error: failed to synthesize instance of type class
  IsGrandparent tom pat

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#check (inferInstance : IsGrandparent tom pat)

-- Query that fails — equivalent to "false" in Prolog:
/--
error: failed to synthesize instance of type class
  IsGrandparent liz ann

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#check (inferInstance : IsGrandparent liz ann)

/- ============================================================
   Ancestor: recursion and the type class resolver
   ============================================================
   In Prolog: ancestor(X,Y) :- parent(X,Y).
              ancestor(X,Y) :- parent(X,Z), ancestor(Z,Y).

   We could try to write this as type class instances:

     class IsAncestor (x : Person) (y : outParam Person)
     instance [IsParent x y] : IsAncestor x y := {}
     instance [IsParent x mid] [IsAncestor mid y] : IsAncestor x y := {}

   But this does NOT work. The type class resolver would loop:
   to find IsAncestor x ?, it tries IsParent x ? → mid, then
   needs IsAncestor mid ? → which again tries IsParent mid ? → ...
   Lean detects the cycle and fails (or hits the recursion limit).

   This is a fundamental limitation: type class resolution is
   a fragment of Prolog that does not support arbitrary recursion.
   Grandparent works because it has fixed depth (two IsParent steps).
   Ancestor requires unbounded depth — exactly what Prolog's
   backtracking search handles but type class resolution cannot. -/

/- ============================================================
   Sibling: the limits of the type class resolver
   ============================================================
   In Prolog:  sibling(X, Y) :- parent(Z, X), parent(Z, Y), X \= Y.

   This is hard with type classes because:
     1. The resolver returns the *first* match, not all of them.
        IsParent tom ? → bob (always), never liz via backtracking.
     2. There is no native negation (X \= Y).

   This illustrates a key point from the paper: type classes are
   a *fragment* of Prolog — they support Horn clauses, but without
   negation and with backtracking limited by outParam.

   Pragmatic solution: explicit facts (which Prolog also does
   internally when expanding the rule). -/

class IsSibling (x y : Person)

instance : IsSibling bob liz := {}
instance : IsSibling liz bob := {}
instance : IsSibling ann pat := {}
instance : IsSibling pat ann := {}

/-- info: inferInstance : IsSibling bob liz -/
#guard_msgs in
#check (inferInstance : IsSibling bob liz)

/-- info: inferInstance : IsSibling ann pat -/
#guard_msgs in
#check (inferInstance : IsSibling ann pat)

/- ============================================================
   Bonus: type classes with data (like Prolog functors)
   ============================================================
   We can associate data with relations, not just existence. -/

class Age (p : Person) where
  age : Nat

instance : Age tom where age := 70
instance : Age bob where age := 45
instance : Age liz where age := 43
instance : Age ann where age := 20
instance : Age pat where age := 18

def ageOf (p : Person) [inst : Age p] : Nat := inst.age

/-- info: 70 -/
#guard_msgs in
#eval ageOf tom

/-- info: 20 -/
#guard_msgs in
#eval ageOf ann
