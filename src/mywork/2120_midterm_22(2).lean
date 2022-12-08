
/-
This is the CS2120 (Sullivan) midterm exam. 

The exam has 100 points total distributed over four
multi-part questions. There's an extra credit question
at the end. Points for each part are indicated.
-/

-- ****************** #1 [30 points] *******************

/- A. [5 points] 

Is it true in predicate logic that  
(false → true) ∧ (false → false)?
Answer: Yes, because false → true is true and false → false is also true,
so then true ∧ true must be true. 


-/

/- B. [10 points] 

Give a formal proof by completing the 
following "example" in Lean, or state 
in English that there is no such proof.

-/

example : (false → true) ∧ (true → true) :=
begin
apply and.intro,
assume f,
apply true.intro,
assume t,
apply true.intro,
end


/- C [15 points]. 

Give an English language proof of the proposition. 
Identify each inference  rule you use at each point
in your argument. For example, at a certain point 
you might say something like this: By the ____ rule, 
it will suffice to show ____. Then you would go on
to show that what remains to be proved is valid. 


Answer:
First, to split up the proposition, we can use the and
elimination rules to show that both (false → true) and
(true → false) must be true. Now, to show that both 
false → true is true and true → true is true. In this case,
we can use the true introduction inference rule to satisfy
both implications, since both implications have a conclusion of true,
we can say that both implications are true, since that's what
true introduction means, and the proof is finished.
-/


-- ****************** #2 [30 points] *******************


/- 
"Resolution" is an inference rule that we 
haven't talked about before. It's valid in
propositional, classical, and constructive
predicate logic. We will present the rule,
in both propositional and predicate logic,
and will ask you to prove that is's valid
in each case.


In propositional logic, the resolution rule 
is ¬P ∨ Q, P ⊢ Q. To check its validity, we 
can write it as  (¬P ∨ Q) ∧ P → Q. Note: ∧ 
has higher precedence than →, so there are 
implicit parentheses around (¬P ∨ Q) ∧ P, 
making the overall proposition an implication.
-/


/- A. [5 points].

Give a brief English language explanation why this
inference rules makes sense: not a rigorous proof,
just an explanation of why Q has to be true under
the conditions give by the assumptions/premises.

Answer: In order for the proposition to return true, in the cases
where Q is true or false, if Q was false, then (¬P ∨ Q) ∧ P would always 
return false, in both cases where P is true or false. In the cases where
Q is true, it doesn't matter what is on the left side, since both
false → true and true → true are both true.

-/



/- B. [5 points]

Prove that this inference rule is valid in
propositional logic by giving a truth table for it. 
We'll give you a start. Fill in the rows then state
how you know from the truth table that the overall
proposition is valid.

P   Q   (¬P ∨ Q)    (¬P ∨ Q) ∧ P    ((¬P ∨ Q) ∧ P) → Q
------------------------------------------------------
f   f   t           f               t
f   t   t           f               t
t   f   f           f               t
t   t   t           t               t


Statement: I know that the overall proposition is valid
since the end goal, the end proposition, is true for
all interpretations of P and Q.

-/  


/- C. [10 points] 

Give a formal proof that the inference rule is 
valid in our constructive predicate logic. Fill
in a proof script here to construct your proof.
Hint: remember that the cases tactic applied to
a proof of a conjunction applied and.elim both
left and right, and when applied to a proof of 
a disjunction gives you two cases to consider,
where you need to show that the remining goal
is true in either case. 
-/

example : ∀ (P Q : Prop), (¬P ∨ Q) ∧ P → Q :=
begin
assume P Q,
assume h,
cases h with left right,
cases left with np q,
contradiction,
apply q,
end


/-
D. [10 points] Give an informal (English) proof 
that the inference rule is valid in predicate logic. 
Name each inference rule you use in your reasoning.

Answer: To start the proof, we first use case analysis to apply 
the and elimination rule, to show that both sides of the ∧ must be true.
Then, since the left side is ¬P ∨ Q, we can use case analysis to apply the 
or elimination rule, to show the case where ¬P could be true and the case
where Q could be true. In the first case, since we had a proof of P already, and
we now had a proof of ¬P, it was a contradiction and false elimination could be used.
In the second case where Q is true, the goal was to find a proof of Q, so that
goal was accomplished as well.
-/


-- ****************** #3 [20 points] *******************


/- 
A. [10 points]. Write formally (in constructive logic) 
the proposition that, for any propositions P and Q, if 
P is equivalent to Q (iff), then if P is true, then Q
is true.  Hint: put parentheses around your ↔ expression. 
-/

-- Don't try to write a proof here; just the proposition
def if_p_iff_q_then_if_also_p_then_q : Prop :=
    ∀ (P Q : Prop), (P ↔ Q) → (P → Q)


/-
B. [10 points] Give *either* a precise, complete English
language proof that this proposition is valid, naming 
each inference you you use in your reasoning, *or* give 
a formal proof of it using Lean. You do not have to give
both. 
-/


/- Option #1: Informal proof:

-/


/-
Option #2: Formal proof. Reminders: the iff elim
rules are called iff.mp and iff.mpr in Lean; or you
can use "cases" to apply the two elimination rules 
to a proof of a bi-implication automatically.
-/

example : if_p_iff_q_then_if_also_p_then_q :=
begin
unfold if_p_iff_q_then_if_also_p_then_q,
assume P Q,
assume pq,
assume p,
cases pq with pimpq qimpp,
apply pimpq p,
end




-- ****************** #4 [20 points] *******************

/- #



A. [10 points] Suppose P is any proposition. In plain
English give a step by step explanation of how you would 
go about proving ¬P using proof *by negation*. 

Answer:
To prove ¬P, which basically means that P → false, I can start
with a proof of ¬P, and then assume that P is true, and from this premise,
I can apply the proof of ¬P onto P and show that it is a contradiction,
and then use false elimination to conclude the proof. 

-/


/- B. [10 points] 

In plain English explain each step in a proof of P
*by contradiction*. Identify where a proof by negation 
(¬ introduction) occurs in the proof by contradiction. 
Explain what classical rule of inference you need to 
use to finish off such a proof. 

Answer: 
To find a proof of P by contradiction, I need to assume ¬P instead. 
If I start by assuming ¬P, but then I show that I already have a 
proof of P, I can show that this leads to a contradiction, and 
use proof by negation here to introduce a ¬ sign onto ¬P, making 
it ¬¬P, and then we use negation elimination to show that ¬¬P → P. 


-/



/- Extra Credit [10 points for all three answers correct]

Suppose that "if it's sunny, it's hot, and also that if 
it's not sunny, it's hot. 


A. Is it hot in classical logic? 

Answer: 


B. Is it hot "constructively?" Briefly explain your answer. 
    
Answer: 


C. Give a formal proof of your answer to the classical question. 
Use S and H as names to stand for the propositions, "it's sunny" 
and "it's hot," where S stands for "it's sunny" and H stands for
"it's hot."
-/

-- it's hot
example : ∀ (S H : Prop), (S → H) → (¬S → H) → H :=
begin
end

