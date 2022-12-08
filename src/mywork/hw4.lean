/-
CS 2120 F22 Homework #4. Due Oct 13.
-/

/- #1A [10 points]

Write a formal proposition stating that 
logical and (∧) is associative. That is, 
for arbitrary propositions, P, Q, and R,
P ∧ (Q ∧ R) is true *iff* (P ∧ Q) ∧ R is, 
too. Replace the placeholder (_) with your
answer.
-/
--and is right associative
def and_associative : Prop := 
  ∀ (P Q R : Prop),

  P ∧ (Q ∧ R) ↔ (P ∧ Q) ∧ R

/- #1B [10 points]

Give an English language proof. Identify
the inference rules of predicate logic
that you use in your reasoning.

In order to satisfy the iff equivalency, the left side must imply the right side 
and vice versa, so we need to prove both sides. If we assume P ∧ (Q ∧ R) is true, we can use case analysis
to see that P must be true and (Q ∧ R) must be true, and then do case analysis again on Q ∧ R to find 
that Q and R are true. Then, we can construct the right side of the proposition by using 
and introduction to find the (P ∧ Q) ∧ R is true as well, by piecing together the individual propositions.
Once the forward case where P ∧ (Q ∧ R) → (P ∧ Q) ∧ R is proven, the vice versa needs to be done,
but the process is the same. Now, we just need to break up the right side using the and elimination rules
and show that P, Q and R are true and show (P ∧ Q) ∧ R → P ∧ (Q ∧ R) to satisfy
iff equivalency.
-/


/-
Answer: 
-/

/- #1C [5 points]

Give a formal proof of the proposition.
Hint: unfold and_associative to start.
-/

theorem and_assoc_true : and_associative :=
begin
unfold and_associative, --expand definition of and_associative
assume P Q R,           --for all intro inference rule
apply iff.intro _ _,    --iff intro, with 2 subgoals
--forward
assume pqr,             --assume premise
cases pqr with p qr,    --unbox proofs of P and of Q ∧ R
cases qr with q r,      -- unbox to get proofs of Q and R
let pq := (and.intro p q), --if you want to build up big proofs from smaller proofs, use let to bind names
apply and.intro pq r,
--reverse direction
assume pqr_right, --now need to prove on the other side
cases pqr_right with pq r,
cases pq with p q,
let qr := (and.intro q r),
apply and.intro p qr,
end



/- #2A [10 points]

Write the proposition that ∨ is associative.,
analogous to the proposition about ∧ in #1.
-/

def or_associative : Prop := 
  ∀ (P Q R), P ∨ (Q ∨ R) ↔ (P ∨ Q) ∨ R

/- #2B [10 points]

Write an English language proof of it, citing
the specific inference rules you use in your
reasoning.

In order to satisfy the iff equivalency, the left side must imply the right side and the 
right side must imply the left side. To start, we need to first use the for all inference rule
to introduce P Q R, and then apply the iff intro, since that is the main connector.
After that, there are two goals, one to show that P → Q → R → (P → Q) → R, and then vice versa.
To show the first goal, I applied the or.intro rules to split up the propositions, using 
case analysis, and then kept applying the or.intro inference rules until it ended with
the individual propositions, and then using the exact keyword.
Then, the same could be done for the second case where the right side implies the left, and 
then or.intro_left/or.intro_right could be applied till the individual propositions are found, and 
then the proof was complete.    
-/


/- #2C [5 points]

Complete the following formal proof.
-/

theorem or_associative_true : or_associative :=
begin
unfold or_associative,
assume P Q R,
apply iff.intro _ _ ,
--forward side
assume pqr_left,
cases pqr_left with p qr,
apply or.intro_left,
apply or.intro_left,
exact p,
cases qr with q r,
apply or.intro_left,
apply or.intro_right,
exact q,
apply or.intro_right,
exact r,

--reverse side
assume pqr_right,
cases pqr_right with pq r,
cases pq with p q,
apply or.intro_left,
exact p,
apply or.intro_right,
apply or.intro_left,
exact q,
apply or.intro_right,
apply or.intro_right,
exact r,

end


/- #3A [10 points]
Write a formal statement of the proposition.
-/

def arrow_transitive : Prop := ∀ (P Q R : Prop), (P → Q) → (Q → R) → (P → R) 

/- #3B [10 points]

Write an English language proof of the proposition
that for any propositions, X, Y, and Z, it's the
case that (X → Y) → (Y → Z) → (X → Z). In other
words, implication is "transitive." Hint: Recall
that if you have a proof of, say, X → Y, and you 
have a proof of X, you can derive a proof of Y by
arrow elimination. Think of it as applying a proof
of an implication to a proof of its premise to get
yourself a proof of its conclusion.

Instead of looking at the proof from the beginning, like X → Y, we can think of the arrow_transitive proof
as proving a function, with each of the implies statements being inputs. Thus, in order for Z to be true,
Y has to be true, since (Y → Z), and in order for Y to be true, X must be true, since (X → Y), so if we looked at in function
form, and yz: Y → Z, xy: X → Y, it would be yz(xy(x)) as the function, where X is the input. Since we assume
X to be true for this proof, then we can conclude that Z is true as well, and if Z is true whenever X is true,
then we can say the X → Z, which gives the proof of arrow transivity.
-/


/- #3C [5 points]. 
Write a formal proof of it.
-/
theorem arrow_transitive_true : arrow_transitive :=
begin 
unfold arrow_transitive,
assume P Q R,
assume pq qr,
assume p,
apply qr,
apply pq,
exact p,
end


/- #4
Suppose that if it's raining then the streets
are wet. This problem requires you to prove that
if the streets are not wet then it's not raining.
-/

/- #4A [10 points]

Start by writing the proposition in predicate
logic by completing the following answer.
-/

def contrapositive : Prop :=
  ∀ (Raining Wet : Prop), 
    (Raining → Wet) → (¬Wet → ¬Raining)


/- #4B [10 points]. 
-/


theorem contrapositive_valid : contrapositive :=
begin
unfold contrapositive,
assume Raining Wet,
assume rw,
--need to show that not raining is true, not wet is true, so need to show proof for not
assume nw,
assume Raining,
let w := rw Raining,
let notwet := nw w,
exact notwet,
end

/- #4C [5 points]. 
To execute the proof, the arrows need to be removed, and this can be done by using
the arrow elimination reference rules until a proof of Raining is found. Then, by applying
the propositions already found in the proposition, such as Raining → Wet or ¬Wet, a proof
of Wet can be found. However, since there is already a proof of ¬Wet, this is a contradiction,
so by using the false elimination rule, the proposition can be proven.

Give an English language proof of it.
-/


/- #5. Extra credit.

Complete the following formal proof of the 
proposition that if for any proposition P, 
P ∨ ¬P is true, then for any propositions, 
X and Y, if it's not the case that X or Y
is true then it is the case that ¬X and ¬Y 
is true. 
-/

theorem demorgan1 : 
  (∀ (P : Prop), P ∨ ¬ P) → 
    ∀ (X Y : Prop), 
      ¬(X ∨ Y) → (¬X ∧ ¬Y) :=
begin
assume em X Y nxory,
cases (em X) with x nx,
let foo := or.intro_left Y x,
_
end

/-
A comment on or.intro_left and or.intro_right.
In Lean each of these takes two arguments: a
proof of the disjunct -- the proposition on 
one side of the ∨ -- that is to be proven true, 
*and* it takes as an argument the proposition 
that is not being proven true. In applications 
of these rules the proposition argument (not 
being proven) comes first, while the proof 
argument comes second.

The reason is that Lean needs to know what 
overall proposition is being proved. From the
proof argument it can infer the proposition 
being proved, but it needs the other proposition
as well to know the full (X ∨ Y) disjunction to
be proved. 

Here's an example:
-/

example : 0 = 0 ∨ 0 = 1 :=
begin
apply or.intro_left (0 = 1) rfl
/-
The "rfl" serves as a proof of 0=0.
But in addition, as the first argument
to or.intro, we need to provide the
*proposition* that is not being proved.
Here's that's (0 = 1). In contexts
where Lean can infer both disuncts,
you can use the simpler or.inl or 
or.inr, each of which just takes one
argument: a proof of the left or of 
the right side, respectively.
-/
end

