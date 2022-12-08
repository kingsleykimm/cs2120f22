
#check @bool.rec_on
example: ∀ (n : bool), bnot (bnot n) = n :=
begin
assume n,
cases n,
apply rfl,
apply rfl,
end

example: ∀ (n : bool), bnot (bnot n) = n :=
begin
assume n,
apply bool.rec_on n, --equivalent to cases, it says that ff and tt must have the listed property

end
#check nat

open nat
--definition of natural numbers:
/-
inductive nat
| zero : nat
| succ (n : nat) : nat
-/

def z := zero
def one := succ z
def two := succ (succ z)
def three := succ(two)

def inc (n' : ℕ ) : ℕ := succ (n')
#eval inc 3
--how to decrement?
def dec : ℕ → ℕ
| zero := zero
| (succ n') := n'

def my_add : ℕ → ℕ → ℕ
| n 0 := n
| n (succ m') := succ (my_add n m')
def my_mul : ℕ → ℕ → ℕ
| n 0 := 0
| n (m+1) := my_add n (my_mul n m) -- n * (1 + m) = n + n * m, recurse down to m = 0

def exp : ℕ → ℕ → ℕ 
| n 0 := 1
| n (succ m) := my_mul n (exp n m)


--  n^3 = n * n^2

