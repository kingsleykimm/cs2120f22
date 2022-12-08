import data.set

/- #1

Formally prove that if there's an object, a, of some 
type, α, having some property (satisfying a predicate), 
P, then not every object of type α fails to have property, 
P. Add a brief comment before each line of your proof 
script to provide what amounts to the outline of a good
English language proof.
-/

example (α : Type) (P : α → Prop) : (∃ a, P a) → (¬(∀ x, ¬ P x)) :=
begin
assume h,
assume x,
cases h with w pf,
let f := x w,
contradiction,
end


/- Extra credit. 

The converse of this proposition is clasically true. If
not every object has propery, P, then there must be some
object that has it. If you try to prove the converse in
our constructive logic, what happens? Show you work, and
then briefly but clearly explain exactly what goes wrong.
-/




/- #2

Consider the following binary relation, r, with domain
and co-domain both being ℕ. For each following question,
answer yes/no then briefly justify your answer.

( domain = ℕ, r = {(0,0),(1,1),(2,2)}, co-domain=ℕ )

A. Is this relation reflexive? 
Yes, since for each value in the relation, 0, 1, 2, there contains a relation to itself,
since the pairs (0, 0), (1, 1), (2, 2) are in r.

B. Is this relation symmetric? 
Yes, since for each of the pairs in r, the reverse relation is also in
the set. For example if we look at the pair (0, 0), and say a = 0 and b = 0, then
the pair b = 0 and a = 0 is also in the relation, and the same can be said for 1 and 2.

C. Is this relation transitive? 
NO, this relation isn't transitive. None of the pairs in the relation have overlapping numbers,
each pair has its own distinct numbers, so there would be no way to prove transitivity.

D. Is this relation an equivalence relation? 
No, it is not an equivalence relation since this relation isn't transitive.
-/



/- #3

A binary relation, r, is said to be *anti-symetric* 
if, for all values in its domain, a and b, if r a b 
and if r b a then a = b. Give an example of a familiar
arithmetic relation that's anti-symmetric, and briefly
explain why it's so.

The ≤ relation is anti-symmetric, since if a ≤ b and b ≤ a are both true,
then that means that a must equal b, or else both propositions wouldn't be satisfied.
-/


/- #4
A binary relation, r, is said to be *asymmetric* if
whenever, for any a and b, if r a b then ¬ r b a. Be
careful to note that asymmetry and antisymmetry are
different properties.  Answer each of the following 
sub-questions. We give you a formal definition of anti
-/

def is_asymmetric 
  {α : Type} 
  (r : α → α → Prop) : Prop 
  := ∀ (a b : α), r a b → ¬ r b a 

/- A.

Name a familar arithmetic relation that's asymmetric
and briefly explain why you think it's asymmetric.

Answer here: An example of an asymmetric relation is <, because if a < b,
then ¬ (b < a) must be true, since it was already defined that a was smaller than b,
so it is impossible for b to be smaller than a.

-/

/- C: 

An object cannot be related to itself in an asymmetric
relation. First, complete the following informal proof
of this statement.

Proof: Assume α, r, and a are as given (and in particular
assume that r is asymmetric). Now assume r a a. <finish
the proof>.

Answer here (rest of proof): 
If we switched the 'order' of the two As in r, and we know that r is asymmetric,
we can say that: r a a = ¬ (r a a). However, this is a contradiction, so we can
use the false elimination rule and complete the proof.
-/

/- D.

Now prove a closely related proposition formally. 
Add a comment to each line of your formal proof 
so as to construct a good skeleton for a fluent 
English language proof.
-/

example
  (α : Type) 
  (r : α → α → Prop)
  (h : is_asymmetric r) :
¬ ∃ (a : α), r a a :=
begin
-- proof by negation
assume e, --assume the proof to show I'm proving for false
cases e with w pf, --apply exists.elim for a witness and proof
let f := h w w, -- put both w as argument for is_asymmetric, w is acting as a here
apply f pf, -- f now takes (r w w) as an argument, so input pf to show that proving false is the same as proving pf
exact pf, -- now just exact the pf I have
end


/- #5
Prove that equality on an inhabited (non-empty) type 
is not assymetric. In the following formalization we
assume there is a value (a : α), which establishes 
that α is inhabited.
-/

example (α : Type) (a : α): ¬is_asymmetric (@eq α)  :=
begin
unfold is_asymmetric,
assume h,
apply h a a,
exact rfl,
exact rfl,
end

/- Extra credit: What exactly goes wrong in a formal 
proof if you drop the "inhibitedness" condition? Give
as much of a formal proof as you can then explain why
it can't be completed (if it can't!).
-/



/- #6
Two natural numbers, p and q, are said to be 
"equivalent mod m" if p % m = q % m, which makes
"equivalence mod m" a binary relation on natural
numbers. Here's a formal definition of this binary
relation on the natural numbers (given an m).
-/

def equiv_mod_m (m : ℕ) : ℕ → ℕ → Prop := 
  λ p q : ℕ, p % m = q % m

/-
Prove using Lean's definition of "equivalence" that 
equiv_mod_m is an equivalence relation for any natural
number, m. Here you'll also use Lean's definitions of
reflexive, symmetric, and transitive. They are as we
have covered in class. 
-/

example : ∀ m : ℕ, equivalence (equiv_mod_m m) :=
begin
intros,
unfold equivalence,
apply and.intro,
unfold reflexive,
unfold equiv_mod_m,
assume x,
exact rfl,
apply and.intro,
unfold symmetric,
unfold equiv_mod_m,
assume x y,
assume h,
rw h,
unfold transitive,
assume x y z,
unfold equiv_mod_m,
assume h1 h2,
rw h1,
rw h2,
end



/- #7
Consider the relation, tin_rel, that associates people 
with U.S. taxpayer id numbers, which we'll represent as 
natural numbers here. 

Assume this relation is single-valued. Which of the 
following properties does this relation have? Give
a very brief justification of each answer. Assume
the domain is all living persons, and the co-domain
is all natural numbers.

-- it's a function: It is a function since this relation is single-valued, each person can has their own id number.
-- it's total: It is total, since every input (person) will have an output (id number).
-- it's injective (where "): It is injective, since it isn't many-to-one -- it is single-valued instead, each person has an unique id number.
-- it's surjective (where the co-domain is all ℕ): No, since not every single natural number / id number will have a person related to it.
-- it's strictly partial: It isn't strictly partial, since if there exists a person, there must exist a id number that person can have.
-- it's bijective: It's not bijective since it isn't surjective.
-/



/- #8
Suppose r is the empty relation on the natural 
numbers. Which of the following properties does
it have? Explain each answer enough to show you
know why your answer is correct.

-- reflexive:
Since the relation is empty, if there does exist a natural number, there would be no relation to itself
that can be found in the empty relation, so it can't be reflexive.
-- symmetric: 
I can prove the relation is symmetric by showing there are no example of it being asymmetric, the
counterexample. Since the relation is empty, there are no possible ways of showing asymmetry, so it is symmetric.
-- transitive:
Just like the proof of symmetry, since the relation is empty, there are no possible counterexamples
of transitivity, so I can assume that the empty relation is transitive.
-/



/- #9
Here's a formal definition of this empty relation.
That there are no constructors given here means there 
are no proofs, which is to say that no pair can be 
proved to be in this relation, so it must be empty.
-/

inductive empty_rel : ℕ → ℕ → Prop

/-
Formally state and prove you answer for each of the
three properties. That is, for each property assert
either that empty_rel does have it or does not have it, 
then prove your assertion. Include English-language 
comments on each line to give the essential elements 
of a good English language proof.
-/


example : ¬reflexive empty_rel :=
begin
unfold reflexive, --unfold the reflexive proof
assume h, --eliminate the not and show proving for false
let x := h 0, --input 0 into h to show that x is the case where empty_rel 0 0
cases x, --use cases to show that empty_rel 0 0 is false, since relation is empty
end

example : symmetric empty_rel :=
begin
unfold symmetric, --unfold the symmetric proof to show variables
assume a b h, --use for all elimination and arrow elimination
cases h, --use cases to show that empty_rel b a exists since the relation is empty
end

example : transitive empty_rel :=
begin
assume a b c h k, -- do for all elimination and arrow elimination to get variables
cases h, --use the proof of h and substitute k into h to show that empty_rel a c
end

/- #10
A relation, r, is said to have the property of being 
a *partial order* if it's reflexive, anti-symmetric,
and transitive. Give a brief English language proof 
that the subset relation on the subsets of any set, 
S (of objects of some type), is a partial order. 

Pf:  
Suppose S is a set, with a ⊆ S and b ⊆ S subsets. Then

1. Reflexive: The subset relation is reflexive when a = S, since S can also be a subset of S, so 
that means that every element that is in S will be in S, so every element in the set will
be related to itself, making it reflexive.
2. Anti-symmetric: If we say that a = S, then a ⊆ S, S ⊆ a, so the relation is anti-symmetric.
3. Transitive: If a and b are both subsets of S, and in the case where a ⊆ b and we know b ⊆ S, we can
prove transitivity, since all of a's elements will be in b, and all of b's elements will be in S, so all of
a's elements will be in S, so a ⊆ b → b ⊆ S → a ⊆ S.


QED.
-/



/- #11 
Finally we return again to DeMorgan's laws, but
now for sets. You'll recall that these "laws" as we
have seent them so far tell us how to distribute ¬  
over ∨ and over ∧. You will also recall that set
intersection (∩) is defined by the conjunction (∧) 
of the membership predicates, set union (∪) by the
disjunction (∨), and set complement (Sᶜ for a set,
S), by negation (¬). It makes sense to hypothesize 
that we can recast DeMorgan's laws in terms of the
distribution of complement over set union and set
intersection. Indeed we can. Your job is to state
and prove (formally) the first DeMorgan laws for 
sets, which states that the complement of a union
of any two sets equals the intersection of their 
complements.

Hint: To prove that two sets are equal, S = T, use
the ext tactic. It applies a bew axiom (called set 
extensionality) that states that to prove S = T it 
suffices to prove S ↔ T, viewing the sets as being
defined by their logical membership predicates. You
know how to handle bi-implications. The rest you 
can do by seeing "not," "and," and "or" in place 
of complement, conjunction, and disjuction, resp.  
-/

example 
  (α : Type) 
  (a b: set α) :
  (a ∪ b)ᶜ = aᶜ ∩ bᶜ := 
begin
ext,
split,

show ¬(x ∈ (a ∪ b)) → x ∉ a ∧ x ∉ b,
show ¬(x ∈ a ∨ x ∈ b) → x ∉ a ∧ x ∉ b,
assume h,
apply and.intro,
assume g,
apply not.elim h,
apply or.intro_left,
apply g,

assume g,
apply not.elim h,
apply or.intro_right,
apply g,

show x ∉ a ∧ x ∉ b → ¬(x ∈ (a ∪ b)),
show x ∉ a ∧ x ∉ b → ¬(x ∈ a ∨ x ∈ b),
assume h,
assume g,
cases h,
cases g,
contradiction,
contradiction,
end


