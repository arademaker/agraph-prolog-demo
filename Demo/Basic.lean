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

/- ---- Proofs as explanations of derivations ----
   Now we *prove* the queries. The compiler verifies! -/
-- ?- grandparent(tom, ann).
example : Grandparent tom ann :=
  Grandparent.intro bob Parent.tom_bob Parent.bob_ann

-- ?- sibling(bob, liz).
example : Sibling bob liz :=
  Sibling.intro tom Parent.tom_bob Parent.tom_liz (by decide)

-- We can also prove that something does *not* hold:
-- ?- grandparent(liz, ann). -> false
example : ¬ Grandparent liz ann := by
  intro ⟨mid, h1, _⟩
  cases h1  -- no Parent constructor starts with liz

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
