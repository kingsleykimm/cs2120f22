section pred_logic

variables X Y Z : Prop

/-
Quick review of predicates. 

A predicate is a proposition with one or more parameters.
A proposition is a predicate with no remaining parameters!

You can think of a predicate it as a function that takes
one or more arguments and that reduces to a proposition
*about those particular values*. 

Here, for example, we define a predicate, called isEven,
that takes a natural number, n, as an argument and that
reduces to ("returns") the proposition, n % 2 = 0, *for
that particular n*.
-/

def isEven : ℕ → Prop :=
begin
assume n,
exact (n%2 = 0)
end 

/-
In fact, in Lean and similar logical programming systems,
a predicate *is* a function, and can thus be applied to an
argument of the specified type.
-/

#reduce isEven 0      -- 0 = 0
#reduce isEven 1      -- 1 = 0
#reduce isEven 2      -- 0 = 0
#reduce isEven 3      -- 1 = 0

/-
Note that the n%2 expression is evaluated automatically.
-/

/-
We will say that one or more values "satisfy" a predicate
when the corresponding proposition is true. In constructive
logic, that means when there's a proof of that proposition.
-/

example : isEven 0 :=
begin
simp [isEven],  -- new tactic: simplify by def'n of isEven
exact rfl,      -- forces reduction, tests equality
-- Yay! 0 is even
end

example : isEven 1 :=
begin
exact rfl,      -- no need for simp, no proof of 1=0
-- Ooooh, 1 is not even
end

-- In fact we can prove the negation
example : ¬isEven 1 :=
begin
assume h,
simp [isEven] at h, -- more tactic fun
cases h,            -- no proofs of h so done
-- Yay! 1 is *not* even (proof by negation)
end

example : isEven 2 :=
begin
exact rfl,
-- Yay! 2 is even.
end


/-
Now let's see syntax alternatives for defining
functions in Lean. We'll stick with the same
"predicate function", giving different names to
avoid conflicts.
-/

/- 
You can use tactic scripts, but you can also 
write exact proof terms. However, in the case
where the value being assigned to an identifier
is a function value, you will use a so-called
"lambda" or "function" expression.
-/

def isEven1 : ℕ → Prop := fun n, n % 2 = 0
def isEven2 : ℕ → Prop := λ n,   n % 2 = 0 

/-
You can pronounce the terms to the right of 
the := as "a function that takes an argument,
n, and returns, (the proposition) n % 2 := 0."
You can add type judgments either for clarity
or if Lean can't infer them from the context.
def isEven : ℕ → Prop := λ (n : ℕ), n%2 = 0.

The fundamental purpose of the λ/fun keyword is
to *bind names to arguments* so that they can be
used in the body/definition of the function. In
this case, we use λ/fun to bind the name n to 
the actual parameter value when this function is
applied to some argument. All of the n's in the
definition are then replaced by that value, and
the resuling expression is reduced to produce a
final result.  

The fun and λ keywords are exactly equivalent.
the use of "lambda" notation goes way back to 
the early days of CS. A key insight that you 
should take away is that "functions are values
too," and a "lambda expression" is a constant,
or literal value, the type of which is just a
function of some kind.
-/

/-
In Lean, you can move argument declarations to
the left of the colon and give them names there,
just as you would in Java or Python.
-/

def isEven3 (n : ℕ) : Prop := n % 2 = 0

/-
And as usual, you can leave out type judgments
when Lean can infer them from context.
-/

def isEven4 (n) := n % 2 = 0 -- parens required

/-
Finally, in Lean, you can use a construct called
"pattern matching" to define functions "by cases."
Here's the syntax. We'll use this syntax quite a
bit going forward, so best to get used to it now. 
-/

def isEven5 : ℕ → Prop    -- NB: No := used here
| n := n % 2 = 0

/-
Here, the "n" is bound to any value of the argument
type, and is then used to define the "return value"
to the right of the :=. In general we can use this
method of function definition to define returns for
different values or combinations of argument values.
-/

def my_bool_and : bool → bool → bool 
| tt tt := tt
| tt ff := ff
| ff ff := ff
| ff tt := ff

def my_bool_and2: bool → bool → bool
| tt tt := tt
| _ _ := ff
/-
Functions in Lean must be "total," which means that
they must be defined to return values of the right
types for *all* possible combinations of arguments.
Go ahead and add the missing cases, then apply your
function!
-/

#eval my_bool_and tt tt
#eval my_bool_and tt ff
#eval my_bool_and ff tt
#eval my_bool_and ff ff

example : my_bool_and tt tt = tt := rfl
example : my_bool_and tt ff = ff := rfl
example : my_bool_and ff tt = ff := rfl
example : my_bool_and ff ff = ff := rfl

def my_bool_not: bool → bool
| tt := ff
| ff := tt

example : my_bool_not ff = tt := rfl

/-
You should (almost must) use this "by cases" syntax
to define functions recursive functions. If you use
other syntax, you'll find that you won't be able to
have the function body call the function itself.
-/

def factorial' (n : ℕ) : ℕ :=
  if n = 0 
  then 1 
  else n * factorial' (n-1)      -- factorial not defined

def factorial : ℕ → ℕ           -- remember, no := here
| 0 := 1 --base case, where if the input matches 0
| (n' + 1) := (n' + 1) * factorial n' --if the input doesn't match 0

--Lean can't prove termination recursive call is passed f(n) for some function, n
def factorial2 : ℕ → ℕ           -- remember, no := here
| 0 := 1 --base case, where if the input matches 0
| n' := n' * factorial2 (n'-1) --doesn't work, since Lean doesn't think n-1 = 1 less than n
#eval factorial 5

--identity function on nat numbers
def id_nat : ℕ → ℕ
| n := n 
def id_string : string → string 
| s:= s 
def id_bool : bool → bool
| b := b 
--can make polymorphic versions in Lean (generics in Java)
def id_T (T : Type) : T → T -- you put (T: Type) before the colon since it's like a function 
                            -- and you're factoring out the Type here, which is T
| t := t

def id_T' : ∀ (T : Type), T → T 
| T t := t

#eval id_T' nat 3

-- ∃

example : ∃ (n : ℕ), isEven n :=
  exists.intro 2 rfl --takes two arguments, a witness and a proof that the witness is even
--any witness will do, as long as it satisfies the predicate
-- the type of the second element depends on the value of the first
-- for example, if first element was 8, need to prove that 8 % 2 = 0
def exists_intro := ∀ {P : X → Prop} (w : X), P w → (∃ (x : X), P x) 
--here, P: X is a predicate that takes X as an argument
-- w is a witness with type X that can be put into function P
-- So when P is applied onto W, and it is valid, then there exists for
-- a proposition x that the predicate P is valid for

--Elim:

example : (∃ (n : ℕ), isEven n) → true :=
begin 
assume h,
-- apply exists.elim h, very complicated
cases h with w pf, --when we use exists.elim, it only knows that there is a witness of type, but doesn't know the actual value
--information hiding construct, the proof doesn't contain any value of the witness

end

variables (Ball : Type) (isBlue : Ball → Prop) (isRound : Ball → Prop)
variables (b : Ball) (b_blue : isBlue b) (b_round : isRound b)

example : ∃ (a_ball : Ball), isBlue a_ball :=
exists.intro b b_blue

def exists_elim := 
  ∀ {X : Type}              -- for any type, X 
    {P : X → Prop}          -- for any predicate on values of this type
    {Y : Prop},             -- for any "concluding" proposition, Y
    (∃ (x : X), P x) →      -- if we're given a proof that there's an x satisfying P
    (∀ (x : X), P x → Y) →  -- then if for every x that satisfies P Y is true
    Y  

example : exists_elim := 
begin 
  unfold exists_elim,
  assume X P,
  assume Y,
  assume exists_x_with_P,
  assume if_any_x_has_P_then_Y,
  cases exists_x_with_P with w pf,
  apply if_any_x_has_P_then_Y w pf,
end
/-
That's it for the fundamental rules of higher-order predicate
logic. The constructive logic versions of the remaining inference
rules we saw in propositional logic are actually theorems, which
means that they can be proved using only the fundamental rules,
which we accept as axioms. An axiom is a proposition accepted as
true without a proof. The inference rules of a logic are accepted
as axioms. The truth of any other proposition in predicate logic
(the foundation for most of mathematics) is proved by applying 
fundamental axioms and previously proved theorems..  
-/
--If there's someone everyone loves, then everyone loves someone
example 
  (Person : Type)
  (Loves : Person → Person → Prop)
  :
  (∃ (p1 : Person), ∀ (p2 : Person), Loves p2 p1) → 
  (∀ (p : Person), ∃ (q : Person), Loves p q) 
  := 
  begin
  assume h,
  cases h with lenny everyone_loves_lenny,
  assume bruce,
  apply exists.intro lenny _, --witness and proof
  apply everyone_loves_lenny bruce,
  end

  /-
  English proof:
  We'll assume there's someone that everyone loves.
  From this, we can assume that there is an arbitary
  person that everyone loves. Now, if we pick an arbitrary person,
  bruce, and now that we have a proof that everyone loves lenny,
  we can apply this proof to bruce to show that bruce loves lenny as well.
  Since bruce is an arbitary but specific person, 'bruce' could be anyone.
  -/