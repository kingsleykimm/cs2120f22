/-
CS2120 Fall 2022 Sullivan. Quiz #1. Edit your answers into
this file using VSCode. Save the file to your *local* hard 
drive (File > Save As > local > ...). Submit it to the Quiz1
assignment on Collab.
-/

/-
#1: For each of the following questions give a yes/no answer 
and then a very brief explanation why that answer is correct.
To explain why your answer is correct, name the specific rule
of inference that tells you it's correct, or explain that 
there is no such valid inference rule.
-/

/-
#1A

If a ball, b, is round *and* b is also red, is b red?

A: yes/no: yes

B: Why? 
If b is round and b is red, then B is red, since using the AND right-elimination rule, we can see that if 
b is round and b is also red, then b must be red. 
#1B

If flowers make you happy and chocolates make you happy,
and I give you flowers *or* I give you chocolates, will
you be happy?

A: yes/no: yes

B: Why?
This uses several inference rules to prove it is true. By starting off with the proof that flowers make me happy and 
chocolates make me happy, this means that the proposition that flowers make me happy and chocolate makes me happy is true.
Then by using and-elimination left and right, I can find that it is true that flowers will make me happy or chocolate will make me happy.
Then by using or-introduction left and right, I can see that by getting flowers or by getting chocolate, it is true that I will be happy.

#1C: If giraffes are just zebras in disguise, then the 
moon is made of green cheese?

A. yes/no: yes

B. Why? 
To convert this into predicate logic, I can say giraffes are just zebras in disguise is one proposition, X, and
the moon is made of green cheese is another proposition, Y, so X → Y. However, we know that giraffes being zebras in 
disguise is false, so since we have a proof of false: false → Y. We can use the false elimintation rule
to say that Y will always be true, so false → Y will always be true, and this statement will always be true as well.

#1D. If x = y implies that 0 = 1, then is it true that
x ≠ y?

A. yes/no: yes

B. Why?
The statement above in predicate logic says (x = y) → (0 = 1). (0 = 1) however is false, and in order for this implies statement 
to be true, x = y must also equal false, since true → false is false, and false → false is true. Thus, if x = y is false, then
x ≠ y, so that is true.

Want to show that x ≠ y is true, or that x = y is false.

#1E. If every zebra has stripes and Zoe is a Zebra then
Zoe has stripes.

A. yes/no: yes

B. Why?
We can use the arrow elimination reference rule to prove this statement, X → Y, X ⊢ Y.
If we say X = (being a zebra) and Y = (having stripes), then since Zoe is a zebra, X is already true for 
her, as it is in the inference rule, so this entails that Y is also true, which says that 
Zoe must have stripes. 

#1F. If Z could be *any* Zebra and Z has stripes, then 
*every* Zebra has stripes.

A. Yes/no: no

B: Why?
If Z is any zebra and it has stripes, then *any* zebra could have stripes, but this does not
entail that *every* zebra must have stripes, it only says that *any* zebra has the possibility
of having stripes. There is no such valid inference rule for showing that a proposition being 
true for *any* object implies it is true for *every* object.


#1G. If whenever the wind blows, the leaves move, and 
the leaves are moving, then the wind is blowing.

A. yes/no: no

B. Why? If whenever the wind blows it means the leaves move, this can be interpreted as 
(wind blowing) → (leaves moving). However, even when X → Y, Y can be true and X can be false
and X → Y will still be true, which is the case of this statement. Here, Y is true, i.e the leaves are moving,
but this doesn't imply that X is true, that the wind is blowing. In order for Y to also imply X,
X ↔ Y would be needed.


#1H: If Gina is nice *or* Gina is tall, and Gina is nice,
then Gina is not tall. (The "or" here is understood to be
the or of predicate logic.)

A. yes/no: no

B. Why?
Since it is using or, we can see that in order for (if Gina is nice or Gina is tall) to be true, then
only one of the propositions in the or need to be true. However, one of the propositions being true
in the or statement does not imply that the other one is false, we have no way of knowing that. The only inference rule
we have for or elimination is one where a third proposition, Z is known to be true, but we don't have
a valid or-elimination inference rule where we can or-elim left and or-elim right.
-/


/- 
#2

Consider the following formula/proposition in propositional
logic: X ∨ ¬Y.

#2A: Is is satisfiable? If so, give a model (a binding of 
the variables to values that makes the expressions true).
Yes, it is satisfiable, a model that works is when X: True and Y: False.

#2B: Is it valid? Explain your answer. 
In order for a model to be valid, its negation needs to be unsatisfiable. In this case, the negation of the proposition
is ¬X ∨ Y. This proposition however is not unsatisfiable, since the interpretation where X: False and Y: True makes the 
propsition true. Thus, since the negation of X ∨ ¬Y is satisfiable, the proposition is not valid.

-/


/-
#3: 

Express the following propositions in predicate logic, by
filling in the blank after the #check command.

If P and Q are arbitrary (any) propositions, then if (P is 
true if and only if Q is true) then if P is true then Q is 
true.
-/

#check ∀ (P Q: Prop), P ↔ Q → (P → Q) 



/-
#4 Translate the following expressions into English.
The #check commands are just Lean commands and can
be ignored here. 
-/


-- A
#check ∀ (n m : ℕ), n < m → m - n > 0

/-
Answer: For all variables n and m that are natural numbers, if n is less than m, then 
m - n will be greater than zero.
-/

-- B

#check ∃ (n : ℕ), ∀ (m : nat), m >= n

/-
Answer: For every natural number m, there exists a natural number n that is smaller or equal
to m. 
-/


-- C

variables (isEven: ℕ → Prop) (isOdd: ℕ → Prop)
#check ∀ (n : ℕ), isEven n ∨ isOdd n

/-
Answer: In the context of isEven and isOdd, which are functions that yield a proposition on any
natural number, for every natural number n, n will either be even or odd.
-/


-- D

#check ∀ (P : Prop), P ∨ ¬P

/-
Answer: For every proposition P, it is true that the disjunction of P and not P will be true, since
one of P or not P will always be true, meaning the OR will also be true.
-/


-- E

#check ∀ (P : Prop), ¬(P ∧ ¬P)

/-
Answer: For every proposition P, the negation of the conjunction of P and not P will always be true.
-/


/-
#5 Extra Credit

Next we define contagion as a proof of a slightly long
proposition. Everything before the comma introduces new
terms, which are then used after the comma to state the
main content of the proposition. 

Using the names we've given to the variables to infer
real-world meanings, state what the logic means in plain
natural English. Please don't just give a verbatim reading
of the formal logic. 

English translation: For every animal a1 that has a virus, if it comes into close contact
with another animal a2, then the animal a2 will also have a virus.
-/

variable contagion : 
  ∀ (Animal : Type) 
  (hasVirus : Animal → Prop) 
  (a1 a2 : Animal) 
  (hasVirus : Animal → Prop)
  (closeContact : Animal → Animal → Prop), 
  hasVirus a1 → closeContact a1 a2 → hasVirus a2


